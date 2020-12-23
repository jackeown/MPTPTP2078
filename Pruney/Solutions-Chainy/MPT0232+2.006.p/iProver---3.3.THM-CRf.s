%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:31:11 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 124 expanded)
%              Number of clauses        :   35 (  49 expanded)
%              Number of leaves         :   12 (  26 expanded)
%              Depth                    :   15
%              Number of atoms          :  145 ( 251 expanded)
%              Number of equality atoms :   85 ( 149 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    inference(negated_conjecture,[],[f37])).

fof(f57,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k1_tarski(X2)
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f65,plain,
    ( ? [X0,X1,X2] :
        ( k2_tarski(X0,X1) != k1_tarski(X2)
        & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) )
   => ( k2_tarski(sK1,sK2) != k1_tarski(sK3)
      & r1_tarski(k2_tarski(sK1,sK2),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( k2_tarski(sK1,sK2) != k1_tarski(sK3)
    & r1_tarski(k2_tarski(sK1,sK2),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f57,f65])).

fof(f110,plain,(
    r1_tarski(k2_tarski(sK1,sK2),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f66])).

fof(f23,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f94,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f23])).

fof(f122,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK3)) ),
    inference(definition_unfolding,[],[f110,f94])).

fof(f36,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f63])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f111,plain,(
    k2_tarski(sK1,sK2) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f66])).

fof(f121,plain,(
    k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(sK3) ),
    inference(definition_unfolding,[],[f111,f94])).

fof(f22,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f18,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f89,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
     => ~ r2_hidden(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f35])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f14,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_38,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_1224,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_36,plain,
    ( ~ r1_tarski(X0,k1_tarski(X1))
    | k1_tarski(X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1225,plain,
    ( k1_tarski(X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_2826,plain,
    ( k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK3)
    | k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1224,c_1225])).

cnf(c_37,negated_conjecture,
    ( k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_3479,plain,
    ( k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2826,c_37])).

cnf(c_27,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1228,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3493,plain,
    ( r1_tarski(k1_tarski(sK1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3479,c_1228])).

cnf(c_23,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1231,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3753,plain,
    ( k1_tarski(sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3493,c_1231])).

cnf(c_32,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_33,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_395,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
    | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ),
    inference(resolution,[status(thm)],[c_32,c_33])).

cnf(c_1223,plain,
    ( k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
    | r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_395])).

cnf(c_6915,plain,
    ( k4_xboole_0(k1_xboole_0,X0) != k1_tarski(sK1)
    | r1_tarski(k2_xboole_0(k1_tarski(sK1),X0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3753,c_1223])).

cnf(c_6918,plain,
    ( k4_xboole_0(k1_xboole_0,X0) != k1_xboole_0
    | r1_tarski(k2_xboole_0(k1_xboole_0,X0),X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6915,c_3753])).

cnf(c_6922,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | r1_tarski(k2_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6918])).

cnf(c_656,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5131,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_xboole_0(X2,X3),X4)
    | X4 != X1
    | k2_xboole_0(X2,X3) != X0 ),
    inference(instantiation,[status(thm)],[c_656])).

cnf(c_5132,plain,
    ( X0 != X1
    | k2_xboole_0(X2,X3) != X4
    | r1_tarski(X4,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X2,X3),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5131])).

cnf(c_5134,plain,
    ( k2_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k2_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5132])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_102,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_18,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_83,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_21,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_74,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_22,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_70,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_72,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_70])).

cnf(c_68,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6922,c_5134,c_102,c_83,c_74,c_72,c_68])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:44:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.59/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/0.97  
% 2.59/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.59/0.97  
% 2.59/0.97  ------  iProver source info
% 2.59/0.97  
% 2.59/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.59/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.59/0.97  git: non_committed_changes: false
% 2.59/0.97  git: last_make_outside_of_git: false
% 2.59/0.97  
% 2.59/0.97  ------ 
% 2.59/0.97  
% 2.59/0.97  ------ Input Options
% 2.59/0.97  
% 2.59/0.97  --out_options                           all
% 2.59/0.97  --tptp_safe_out                         true
% 2.59/0.97  --problem_path                          ""
% 2.59/0.97  --include_path                          ""
% 2.59/0.97  --clausifier                            res/vclausify_rel
% 2.59/0.97  --clausifier_options                    --mode clausify
% 2.59/0.97  --stdin                                 false
% 2.59/0.97  --stats_out                             all
% 2.59/0.97  
% 2.59/0.97  ------ General Options
% 2.59/0.97  
% 2.59/0.97  --fof                                   false
% 2.59/0.97  --time_out_real                         305.
% 2.59/0.97  --time_out_virtual                      -1.
% 2.59/0.97  --symbol_type_check                     false
% 2.59/0.97  --clausify_out                          false
% 2.59/0.97  --sig_cnt_out                           false
% 2.59/0.97  --trig_cnt_out                          false
% 2.59/0.97  --trig_cnt_out_tolerance                1.
% 2.59/0.97  --trig_cnt_out_sk_spl                   false
% 2.59/0.97  --abstr_cl_out                          false
% 2.59/0.97  
% 2.59/0.97  ------ Global Options
% 2.59/0.97  
% 2.59/0.97  --schedule                              default
% 2.59/0.97  --add_important_lit                     false
% 2.59/0.97  --prop_solver_per_cl                    1000
% 2.59/0.97  --min_unsat_core                        false
% 2.59/0.97  --soft_assumptions                      false
% 2.59/0.97  --soft_lemma_size                       3
% 2.59/0.97  --prop_impl_unit_size                   0
% 2.59/0.97  --prop_impl_unit                        []
% 2.59/0.97  --share_sel_clauses                     true
% 2.59/0.97  --reset_solvers                         false
% 2.59/0.97  --bc_imp_inh                            [conj_cone]
% 2.59/0.97  --conj_cone_tolerance                   3.
% 2.59/0.97  --extra_neg_conj                        none
% 2.59/0.97  --large_theory_mode                     true
% 2.59/0.97  --prolific_symb_bound                   200
% 2.59/0.97  --lt_threshold                          2000
% 2.59/0.97  --clause_weak_htbl                      true
% 2.59/0.97  --gc_record_bc_elim                     false
% 2.59/0.97  
% 2.59/0.97  ------ Preprocessing Options
% 2.59/0.97  
% 2.59/0.97  --preprocessing_flag                    true
% 2.59/0.97  --time_out_prep_mult                    0.1
% 2.59/0.97  --splitting_mode                        input
% 2.59/0.97  --splitting_grd                         true
% 2.59/0.97  --splitting_cvd                         false
% 2.59/0.97  --splitting_cvd_svl                     false
% 2.59/0.97  --splitting_nvd                         32
% 2.59/0.97  --sub_typing                            true
% 2.59/0.97  --prep_gs_sim                           true
% 2.59/0.97  --prep_unflatten                        true
% 2.59/0.97  --prep_res_sim                          true
% 2.59/0.97  --prep_upred                            true
% 2.59/0.97  --prep_sem_filter                       exhaustive
% 2.59/0.97  --prep_sem_filter_out                   false
% 2.59/0.97  --pred_elim                             true
% 2.59/0.97  --res_sim_input                         true
% 2.59/0.97  --eq_ax_congr_red                       true
% 2.59/0.97  --pure_diseq_elim                       true
% 2.59/0.97  --brand_transform                       false
% 2.59/0.97  --non_eq_to_eq                          false
% 2.59/0.97  --prep_def_merge                        true
% 2.59/0.97  --prep_def_merge_prop_impl              false
% 2.59/0.97  --prep_def_merge_mbd                    true
% 2.59/0.97  --prep_def_merge_tr_red                 false
% 2.59/0.97  --prep_def_merge_tr_cl                  false
% 2.59/0.97  --smt_preprocessing                     true
% 2.59/0.97  --smt_ac_axioms                         fast
% 2.59/0.97  --preprocessed_out                      false
% 2.59/0.97  --preprocessed_stats                    false
% 2.59/0.97  
% 2.59/0.97  ------ Abstraction refinement Options
% 2.59/0.97  
% 2.59/0.97  --abstr_ref                             []
% 2.59/0.97  --abstr_ref_prep                        false
% 2.59/0.97  --abstr_ref_until_sat                   false
% 2.59/0.97  --abstr_ref_sig_restrict                funpre
% 2.59/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.59/0.97  --abstr_ref_under                       []
% 2.59/0.97  
% 2.59/0.97  ------ SAT Options
% 2.59/0.97  
% 2.59/0.97  --sat_mode                              false
% 2.59/0.97  --sat_fm_restart_options                ""
% 2.59/0.97  --sat_gr_def                            false
% 2.59/0.97  --sat_epr_types                         true
% 2.59/0.97  --sat_non_cyclic_types                  false
% 2.59/0.97  --sat_finite_models                     false
% 2.59/0.97  --sat_fm_lemmas                         false
% 2.59/0.97  --sat_fm_prep                           false
% 2.59/0.97  --sat_fm_uc_incr                        true
% 2.59/0.97  --sat_out_model                         small
% 2.59/0.97  --sat_out_clauses                       false
% 2.59/0.97  
% 2.59/0.97  ------ QBF Options
% 2.59/0.97  
% 2.59/0.97  --qbf_mode                              false
% 2.59/0.97  --qbf_elim_univ                         false
% 2.59/0.97  --qbf_dom_inst                          none
% 2.59/0.97  --qbf_dom_pre_inst                      false
% 2.59/0.97  --qbf_sk_in                             false
% 2.59/0.97  --qbf_pred_elim                         true
% 2.59/0.97  --qbf_split                             512
% 2.59/0.97  
% 2.59/0.97  ------ BMC1 Options
% 2.59/0.97  
% 2.59/0.97  --bmc1_incremental                      false
% 2.59/0.97  --bmc1_axioms                           reachable_all
% 2.59/0.97  --bmc1_min_bound                        0
% 2.59/0.97  --bmc1_max_bound                        -1
% 2.59/0.97  --bmc1_max_bound_default                -1
% 2.59/0.97  --bmc1_symbol_reachability              true
% 2.59/0.97  --bmc1_property_lemmas                  false
% 2.59/0.97  --bmc1_k_induction                      false
% 2.59/0.97  --bmc1_non_equiv_states                 false
% 2.59/0.97  --bmc1_deadlock                         false
% 2.59/0.97  --bmc1_ucm                              false
% 2.59/0.97  --bmc1_add_unsat_core                   none
% 2.59/0.97  --bmc1_unsat_core_children              false
% 2.59/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.59/0.97  --bmc1_out_stat                         full
% 2.59/0.97  --bmc1_ground_init                      false
% 2.59/0.97  --bmc1_pre_inst_next_state              false
% 2.59/0.97  --bmc1_pre_inst_state                   false
% 2.59/0.97  --bmc1_pre_inst_reach_state             false
% 2.59/0.97  --bmc1_out_unsat_core                   false
% 2.59/0.97  --bmc1_aig_witness_out                  false
% 2.59/0.97  --bmc1_verbose                          false
% 2.59/0.97  --bmc1_dump_clauses_tptp                false
% 2.59/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.59/0.97  --bmc1_dump_file                        -
% 2.59/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.59/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.59/0.97  --bmc1_ucm_extend_mode                  1
% 2.59/0.97  --bmc1_ucm_init_mode                    2
% 2.59/0.97  --bmc1_ucm_cone_mode                    none
% 2.59/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.59/0.97  --bmc1_ucm_relax_model                  4
% 2.59/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.59/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.59/0.97  --bmc1_ucm_layered_model                none
% 2.59/0.97  --bmc1_ucm_max_lemma_size               10
% 2.59/0.97  
% 2.59/0.97  ------ AIG Options
% 2.59/0.97  
% 2.59/0.97  --aig_mode                              false
% 2.59/0.97  
% 2.59/0.97  ------ Instantiation Options
% 2.59/0.97  
% 2.59/0.97  --instantiation_flag                    true
% 2.59/0.97  --inst_sos_flag                         false
% 2.59/0.97  --inst_sos_phase                        true
% 2.59/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.59/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.59/0.97  --inst_lit_sel_side                     num_symb
% 2.59/0.97  --inst_solver_per_active                1400
% 2.59/0.97  --inst_solver_calls_frac                1.
% 2.59/0.97  --inst_passive_queue_type               priority_queues
% 2.59/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.59/0.97  --inst_passive_queues_freq              [25;2]
% 2.59/0.97  --inst_dismatching                      true
% 2.59/0.97  --inst_eager_unprocessed_to_passive     true
% 2.59/0.97  --inst_prop_sim_given                   true
% 2.59/0.97  --inst_prop_sim_new                     false
% 2.59/0.97  --inst_subs_new                         false
% 2.59/0.97  --inst_eq_res_simp                      false
% 2.59/0.97  --inst_subs_given                       false
% 2.59/0.97  --inst_orphan_elimination               true
% 2.59/0.97  --inst_learning_loop_flag               true
% 2.59/0.97  --inst_learning_start                   3000
% 2.59/0.97  --inst_learning_factor                  2
% 2.59/0.97  --inst_start_prop_sim_after_learn       3
% 2.59/0.97  --inst_sel_renew                        solver
% 2.59/0.97  --inst_lit_activity_flag                true
% 2.59/0.97  --inst_restr_to_given                   false
% 2.59/0.97  --inst_activity_threshold               500
% 2.59/0.97  --inst_out_proof                        true
% 2.59/0.97  
% 2.59/0.97  ------ Resolution Options
% 2.59/0.97  
% 2.59/0.97  --resolution_flag                       true
% 2.59/0.97  --res_lit_sel                           adaptive
% 2.59/0.97  --res_lit_sel_side                      none
% 2.59/0.97  --res_ordering                          kbo
% 2.59/0.97  --res_to_prop_solver                    active
% 2.59/0.97  --res_prop_simpl_new                    false
% 2.59/0.97  --res_prop_simpl_given                  true
% 2.59/0.97  --res_passive_queue_type                priority_queues
% 2.59/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.59/0.97  --res_passive_queues_freq               [15;5]
% 2.59/0.97  --res_forward_subs                      full
% 2.59/0.97  --res_backward_subs                     full
% 2.59/0.97  --res_forward_subs_resolution           true
% 2.59/0.97  --res_backward_subs_resolution          true
% 2.59/0.97  --res_orphan_elimination                true
% 2.59/0.97  --res_time_limit                        2.
% 2.59/0.97  --res_out_proof                         true
% 2.59/0.97  
% 2.59/0.97  ------ Superposition Options
% 2.59/0.97  
% 2.59/0.97  --superposition_flag                    true
% 2.59/0.97  --sup_passive_queue_type                priority_queues
% 2.59/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.59/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.59/0.97  --demod_completeness_check              fast
% 2.59/0.97  --demod_use_ground                      true
% 2.59/0.97  --sup_to_prop_solver                    passive
% 2.59/0.97  --sup_prop_simpl_new                    true
% 2.59/0.97  --sup_prop_simpl_given                  true
% 2.59/0.97  --sup_fun_splitting                     false
% 2.59/0.97  --sup_smt_interval                      50000
% 2.59/0.97  
% 2.59/0.97  ------ Superposition Simplification Setup
% 2.59/0.97  
% 2.59/0.97  --sup_indices_passive                   []
% 2.59/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.59/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.97  --sup_full_bw                           [BwDemod]
% 2.59/0.97  --sup_immed_triv                        [TrivRules]
% 2.59/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.59/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.97  --sup_immed_bw_main                     []
% 2.59/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.59/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.97  
% 2.59/0.97  ------ Combination Options
% 2.59/0.97  
% 2.59/0.97  --comb_res_mult                         3
% 2.59/0.97  --comb_sup_mult                         2
% 2.59/0.97  --comb_inst_mult                        10
% 2.59/0.97  
% 2.59/0.97  ------ Debug Options
% 2.59/0.97  
% 2.59/0.97  --dbg_backtrace                         false
% 2.59/0.97  --dbg_dump_prop_clauses                 false
% 2.59/0.97  --dbg_dump_prop_clauses_file            -
% 2.59/0.97  --dbg_out_stat                          false
% 2.59/0.97  ------ Parsing...
% 2.59/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.59/0.97  
% 2.59/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.59/0.97  
% 2.59/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.59/0.97  
% 2.59/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.59/0.97  ------ Proving...
% 2.59/0.97  ------ Problem Properties 
% 2.59/0.97  
% 2.59/0.97  
% 2.59/0.97  clauses                                 37
% 2.59/0.97  conjectures                             2
% 2.59/0.97  EPR                                     4
% 2.59/0.97  Horn                                    34
% 2.59/0.97  unary                                   18
% 2.59/0.97  binary                                  13
% 2.59/0.97  lits                                    65
% 2.59/0.97  lits eq                                 22
% 2.59/0.97  fd_pure                                 0
% 2.59/0.97  fd_pseudo                               0
% 2.59/0.97  fd_cond                                 1
% 2.59/0.97  fd_pseudo_cond                          5
% 2.59/0.97  AC symbols                              0
% 2.59/0.97  
% 2.59/0.97  ------ Schedule dynamic 5 is on 
% 2.59/0.97  
% 2.59/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.59/0.97  
% 2.59/0.97  
% 2.59/0.97  ------ 
% 2.59/0.97  Current options:
% 2.59/0.97  ------ 
% 2.59/0.97  
% 2.59/0.97  ------ Input Options
% 2.59/0.97  
% 2.59/0.97  --out_options                           all
% 2.59/0.97  --tptp_safe_out                         true
% 2.59/0.97  --problem_path                          ""
% 2.59/0.97  --include_path                          ""
% 2.59/0.97  --clausifier                            res/vclausify_rel
% 2.59/0.97  --clausifier_options                    --mode clausify
% 2.59/0.97  --stdin                                 false
% 2.59/0.97  --stats_out                             all
% 2.59/0.97  
% 2.59/0.97  ------ General Options
% 2.59/0.97  
% 2.59/0.97  --fof                                   false
% 2.59/0.97  --time_out_real                         305.
% 2.59/0.97  --time_out_virtual                      -1.
% 2.59/0.97  --symbol_type_check                     false
% 2.59/0.97  --clausify_out                          false
% 2.59/0.97  --sig_cnt_out                           false
% 2.59/0.97  --trig_cnt_out                          false
% 2.59/0.97  --trig_cnt_out_tolerance                1.
% 2.59/0.97  --trig_cnt_out_sk_spl                   false
% 2.59/0.97  --abstr_cl_out                          false
% 2.59/0.97  
% 2.59/0.97  ------ Global Options
% 2.59/0.97  
% 2.59/0.97  --schedule                              default
% 2.59/0.97  --add_important_lit                     false
% 2.59/0.97  --prop_solver_per_cl                    1000
% 2.59/0.97  --min_unsat_core                        false
% 2.59/0.97  --soft_assumptions                      false
% 2.59/0.97  --soft_lemma_size                       3
% 2.59/0.97  --prop_impl_unit_size                   0
% 2.59/0.97  --prop_impl_unit                        []
% 2.59/0.97  --share_sel_clauses                     true
% 2.59/0.97  --reset_solvers                         false
% 2.59/0.97  --bc_imp_inh                            [conj_cone]
% 2.59/0.97  --conj_cone_tolerance                   3.
% 2.59/0.97  --extra_neg_conj                        none
% 2.59/0.97  --large_theory_mode                     true
% 2.59/0.97  --prolific_symb_bound                   200
% 2.59/0.97  --lt_threshold                          2000
% 2.59/0.97  --clause_weak_htbl                      true
% 2.59/0.97  --gc_record_bc_elim                     false
% 2.59/0.97  
% 2.59/0.97  ------ Preprocessing Options
% 2.59/0.97  
% 2.59/0.97  --preprocessing_flag                    true
% 2.59/0.97  --time_out_prep_mult                    0.1
% 2.59/0.97  --splitting_mode                        input
% 2.59/0.97  --splitting_grd                         true
% 2.59/0.97  --splitting_cvd                         false
% 2.59/0.97  --splitting_cvd_svl                     false
% 2.59/0.97  --splitting_nvd                         32
% 2.59/0.97  --sub_typing                            true
% 2.59/0.97  --prep_gs_sim                           true
% 2.59/0.97  --prep_unflatten                        true
% 2.59/0.97  --prep_res_sim                          true
% 2.59/0.97  --prep_upred                            true
% 2.59/0.97  --prep_sem_filter                       exhaustive
% 2.59/0.97  --prep_sem_filter_out                   false
% 2.59/0.97  --pred_elim                             true
% 2.59/0.97  --res_sim_input                         true
% 2.59/0.97  --eq_ax_congr_red                       true
% 2.59/0.97  --pure_diseq_elim                       true
% 2.59/0.97  --brand_transform                       false
% 2.59/0.97  --non_eq_to_eq                          false
% 2.59/0.97  --prep_def_merge                        true
% 2.59/0.97  --prep_def_merge_prop_impl              false
% 2.59/0.97  --prep_def_merge_mbd                    true
% 2.59/0.97  --prep_def_merge_tr_red                 false
% 2.59/0.97  --prep_def_merge_tr_cl                  false
% 2.59/0.97  --smt_preprocessing                     true
% 2.59/0.97  --smt_ac_axioms                         fast
% 2.59/0.97  --preprocessed_out                      false
% 2.59/0.97  --preprocessed_stats                    false
% 2.59/0.97  
% 2.59/0.97  ------ Abstraction refinement Options
% 2.59/0.97  
% 2.59/0.97  --abstr_ref                             []
% 2.59/0.97  --abstr_ref_prep                        false
% 2.59/0.97  --abstr_ref_until_sat                   false
% 2.59/0.97  --abstr_ref_sig_restrict                funpre
% 2.59/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.59/0.97  --abstr_ref_under                       []
% 2.59/0.97  
% 2.59/0.97  ------ SAT Options
% 2.59/0.97  
% 2.59/0.97  --sat_mode                              false
% 2.59/0.97  --sat_fm_restart_options                ""
% 2.59/0.97  --sat_gr_def                            false
% 2.59/0.97  --sat_epr_types                         true
% 2.59/0.97  --sat_non_cyclic_types                  false
% 2.59/0.97  --sat_finite_models                     false
% 2.59/0.97  --sat_fm_lemmas                         false
% 2.59/0.97  --sat_fm_prep                           false
% 2.59/0.97  --sat_fm_uc_incr                        true
% 2.59/0.97  --sat_out_model                         small
% 2.59/0.97  --sat_out_clauses                       false
% 2.59/0.97  
% 2.59/0.97  ------ QBF Options
% 2.59/0.97  
% 2.59/0.97  --qbf_mode                              false
% 2.59/0.97  --qbf_elim_univ                         false
% 2.59/0.97  --qbf_dom_inst                          none
% 2.59/0.97  --qbf_dom_pre_inst                      false
% 2.59/0.97  --qbf_sk_in                             false
% 2.59/0.97  --qbf_pred_elim                         true
% 2.59/0.97  --qbf_split                             512
% 2.59/0.97  
% 2.59/0.97  ------ BMC1 Options
% 2.59/0.97  
% 2.59/0.97  --bmc1_incremental                      false
% 2.59/0.97  --bmc1_axioms                           reachable_all
% 2.59/0.97  --bmc1_min_bound                        0
% 2.59/0.97  --bmc1_max_bound                        -1
% 2.59/0.97  --bmc1_max_bound_default                -1
% 2.59/0.97  --bmc1_symbol_reachability              true
% 2.59/0.97  --bmc1_property_lemmas                  false
% 2.59/0.97  --bmc1_k_induction                      false
% 2.59/0.97  --bmc1_non_equiv_states                 false
% 2.59/0.97  --bmc1_deadlock                         false
% 2.59/0.97  --bmc1_ucm                              false
% 2.59/0.97  --bmc1_add_unsat_core                   none
% 2.59/0.97  --bmc1_unsat_core_children              false
% 2.59/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.59/0.97  --bmc1_out_stat                         full
% 2.59/0.97  --bmc1_ground_init                      false
% 2.59/0.97  --bmc1_pre_inst_next_state              false
% 2.59/0.97  --bmc1_pre_inst_state                   false
% 2.59/0.97  --bmc1_pre_inst_reach_state             false
% 2.59/0.97  --bmc1_out_unsat_core                   false
% 2.59/0.97  --bmc1_aig_witness_out                  false
% 2.59/0.97  --bmc1_verbose                          false
% 2.59/0.97  --bmc1_dump_clauses_tptp                false
% 2.59/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.59/0.97  --bmc1_dump_file                        -
% 2.59/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.59/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.59/0.97  --bmc1_ucm_extend_mode                  1
% 2.59/0.97  --bmc1_ucm_init_mode                    2
% 2.59/0.97  --bmc1_ucm_cone_mode                    none
% 2.59/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.59/0.97  --bmc1_ucm_relax_model                  4
% 2.59/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.59/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.59/0.97  --bmc1_ucm_layered_model                none
% 2.59/0.97  --bmc1_ucm_max_lemma_size               10
% 2.59/0.97  
% 2.59/0.97  ------ AIG Options
% 2.59/0.97  
% 2.59/0.97  --aig_mode                              false
% 2.59/0.97  
% 2.59/0.97  ------ Instantiation Options
% 2.59/0.97  
% 2.59/0.97  --instantiation_flag                    true
% 2.59/0.97  --inst_sos_flag                         false
% 2.59/0.97  --inst_sos_phase                        true
% 2.59/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.59/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.59/0.97  --inst_lit_sel_side                     none
% 2.59/0.97  --inst_solver_per_active                1400
% 2.59/0.97  --inst_solver_calls_frac                1.
% 2.59/0.97  --inst_passive_queue_type               priority_queues
% 2.59/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.59/0.97  --inst_passive_queues_freq              [25;2]
% 2.59/0.97  --inst_dismatching                      true
% 2.59/0.97  --inst_eager_unprocessed_to_passive     true
% 2.59/0.97  --inst_prop_sim_given                   true
% 2.59/0.97  --inst_prop_sim_new                     false
% 2.59/0.97  --inst_subs_new                         false
% 2.59/0.97  --inst_eq_res_simp                      false
% 2.59/0.97  --inst_subs_given                       false
% 2.59/0.97  --inst_orphan_elimination               true
% 2.59/0.97  --inst_learning_loop_flag               true
% 2.59/0.97  --inst_learning_start                   3000
% 2.59/0.97  --inst_learning_factor                  2
% 2.59/0.97  --inst_start_prop_sim_after_learn       3
% 2.59/0.97  --inst_sel_renew                        solver
% 2.59/0.97  --inst_lit_activity_flag                true
% 2.59/0.97  --inst_restr_to_given                   false
% 2.59/0.97  --inst_activity_threshold               500
% 2.59/0.97  --inst_out_proof                        true
% 2.59/0.97  
% 2.59/0.97  ------ Resolution Options
% 2.59/0.97  
% 2.59/0.97  --resolution_flag                       false
% 2.59/0.97  --res_lit_sel                           adaptive
% 2.59/0.97  --res_lit_sel_side                      none
% 2.59/0.97  --res_ordering                          kbo
% 2.59/0.97  --res_to_prop_solver                    active
% 2.59/0.97  --res_prop_simpl_new                    false
% 2.59/0.97  --res_prop_simpl_given                  true
% 2.59/0.97  --res_passive_queue_type                priority_queues
% 2.59/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.59/0.97  --res_passive_queues_freq               [15;5]
% 2.59/0.97  --res_forward_subs                      full
% 2.59/0.97  --res_backward_subs                     full
% 2.59/0.97  --res_forward_subs_resolution           true
% 2.59/0.97  --res_backward_subs_resolution          true
% 2.59/0.97  --res_orphan_elimination                true
% 2.59/0.97  --res_time_limit                        2.
% 2.59/0.97  --res_out_proof                         true
% 2.59/0.97  
% 2.59/0.97  ------ Superposition Options
% 2.59/0.97  
% 2.59/0.97  --superposition_flag                    true
% 2.59/0.97  --sup_passive_queue_type                priority_queues
% 2.59/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.59/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.59/0.97  --demod_completeness_check              fast
% 2.59/0.97  --demod_use_ground                      true
% 2.59/0.97  --sup_to_prop_solver                    passive
% 2.59/0.97  --sup_prop_simpl_new                    true
% 2.59/0.97  --sup_prop_simpl_given                  true
% 2.59/0.97  --sup_fun_splitting                     false
% 2.59/0.97  --sup_smt_interval                      50000
% 2.59/0.97  
% 2.59/0.97  ------ Superposition Simplification Setup
% 2.59/0.97  
% 2.59/0.97  --sup_indices_passive                   []
% 2.59/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.59/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.97  --sup_full_bw                           [BwDemod]
% 2.59/0.97  --sup_immed_triv                        [TrivRules]
% 2.59/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.59/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.97  --sup_immed_bw_main                     []
% 2.59/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.59/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.97  
% 2.59/0.97  ------ Combination Options
% 2.59/0.97  
% 2.59/0.97  --comb_res_mult                         3
% 2.59/0.97  --comb_sup_mult                         2
% 2.59/0.97  --comb_inst_mult                        10
% 2.59/0.97  
% 2.59/0.97  ------ Debug Options
% 2.59/0.97  
% 2.59/0.97  --dbg_backtrace                         false
% 2.59/0.97  --dbg_dump_prop_clauses                 false
% 2.59/0.97  --dbg_dump_prop_clauses_file            -
% 2.59/0.97  --dbg_out_stat                          false
% 2.59/0.97  
% 2.59/0.97  
% 2.59/0.97  
% 2.59/0.97  
% 2.59/0.97  ------ Proving...
% 2.59/0.97  
% 2.59/0.97  
% 2.59/0.97  % SZS status Theorem for theBenchmark.p
% 2.59/0.97  
% 2.59/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.59/0.97  
% 2.59/0.97  fof(f37,conjecture,(
% 2.59/0.97    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 2.59/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.97  
% 2.59/0.97  fof(f38,negated_conjecture,(
% 2.59/0.97    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 2.59/0.97    inference(negated_conjecture,[],[f37])).
% 2.59/0.97  
% 2.59/0.97  fof(f57,plain,(
% 2.59/0.97    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k1_tarski(X2) & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 2.59/0.97    inference(ennf_transformation,[],[f38])).
% 2.59/0.97  
% 2.59/0.97  fof(f65,plain,(
% 2.59/0.97    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k1_tarski(X2) & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))) => (k2_tarski(sK1,sK2) != k1_tarski(sK3) & r1_tarski(k2_tarski(sK1,sK2),k1_tarski(sK3)))),
% 2.59/0.97    introduced(choice_axiom,[])).
% 2.59/0.97  
% 2.59/0.97  fof(f66,plain,(
% 2.59/0.97    k2_tarski(sK1,sK2) != k1_tarski(sK3) & r1_tarski(k2_tarski(sK1,sK2),k1_tarski(sK3))),
% 2.59/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f57,f65])).
% 2.59/0.97  
% 2.59/0.97  fof(f110,plain,(
% 2.59/0.97    r1_tarski(k2_tarski(sK1,sK2),k1_tarski(sK3))),
% 2.59/0.97    inference(cnf_transformation,[],[f66])).
% 2.59/0.97  
% 2.59/0.97  fof(f23,axiom,(
% 2.59/0.97    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 2.59/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.97  
% 2.59/0.97  fof(f94,plain,(
% 2.59/0.97    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 2.59/0.97    inference(cnf_transformation,[],[f23])).
% 2.59/0.97  
% 2.59/0.97  fof(f122,plain,(
% 2.59/0.97    r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK3))),
% 2.59/0.97    inference(definition_unfolding,[],[f110,f94])).
% 2.59/0.97  
% 2.59/0.97  fof(f36,axiom,(
% 2.59/0.97    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.59/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.97  
% 2.59/0.97  fof(f63,plain,(
% 2.59/0.97    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.59/0.97    inference(nnf_transformation,[],[f36])).
% 2.59/0.97  
% 2.59/0.97  fof(f64,plain,(
% 2.59/0.97    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.59/0.97    inference(flattening,[],[f63])).
% 2.59/0.97  
% 2.59/0.97  fof(f107,plain,(
% 2.59/0.97    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.59/0.97    inference(cnf_transformation,[],[f64])).
% 2.59/0.97  
% 2.59/0.97  fof(f111,plain,(
% 2.59/0.97    k2_tarski(sK1,sK2) != k1_tarski(sK3)),
% 2.59/0.97    inference(cnf_transformation,[],[f66])).
% 2.59/0.97  
% 2.59/0.97  fof(f121,plain,(
% 2.59/0.97    k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(sK3)),
% 2.59/0.97    inference(definition_unfolding,[],[f111,f94])).
% 2.59/0.97  
% 2.59/0.97  fof(f22,axiom,(
% 2.59/0.97    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.59/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.97  
% 2.59/0.97  fof(f93,plain,(
% 2.59/0.97    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.59/0.97    inference(cnf_transformation,[],[f22])).
% 2.59/0.97  
% 2.59/0.97  fof(f18,axiom,(
% 2.59/0.97    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.59/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.97  
% 2.59/0.97  fof(f52,plain,(
% 2.59/0.97    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.59/0.97    inference(ennf_transformation,[],[f18])).
% 2.59/0.97  
% 2.59/0.97  fof(f89,plain,(
% 2.59/0.97    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.59/0.97    inference(cnf_transformation,[],[f52])).
% 2.59/0.97  
% 2.59/0.97  fof(f34,axiom,(
% 2.59/0.97    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 2.59/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.97  
% 2.59/0.97  fof(f55,plain,(
% 2.59/0.97    ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 2.59/0.97    inference(ennf_transformation,[],[f34])).
% 2.59/0.97  
% 2.59/0.97  fof(f105,plain,(
% 2.59/0.97    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)) )),
% 2.59/0.97    inference(cnf_transformation,[],[f55])).
% 2.59/0.97  
% 2.59/0.97  fof(f35,axiom,(
% 2.59/0.97    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) <=> ~r2_hidden(X0,X1))),
% 2.59/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.97  
% 2.59/0.97  fof(f40,plain,(
% 2.59/0.97    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) => ~r2_hidden(X0,X1))),
% 2.59/0.97    inference(unused_predicate_definition_removal,[],[f35])).
% 2.59/0.97  
% 2.59/0.97  fof(f56,plain,(
% 2.59/0.97    ! [X0,X1] : (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0))),
% 2.59/0.97    inference(ennf_transformation,[],[f40])).
% 2.59/0.97  
% 2.59/0.97  fof(f106,plain,(
% 2.59/0.97    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)) )),
% 2.59/0.97    inference(cnf_transformation,[],[f56])).
% 2.59/0.97  
% 2.59/0.97  fof(f7,axiom,(
% 2.59/0.97    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.59/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.97  
% 2.59/0.97  fof(f43,plain,(
% 2.59/0.97    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.59/0.97    inference(ennf_transformation,[],[f7])).
% 2.59/0.97  
% 2.59/0.97  fof(f75,plain,(
% 2.59/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.59/0.97    inference(cnf_transformation,[],[f43])).
% 2.59/0.97  
% 2.59/0.97  fof(f14,axiom,(
% 2.59/0.97    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.59/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.97  
% 2.59/0.97  fof(f84,plain,(
% 2.59/0.97    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.59/0.97    inference(cnf_transformation,[],[f14])).
% 2.59/0.97  
% 2.59/0.97  fof(f17,axiom,(
% 2.59/0.97    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.59/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.59/0.97  
% 2.59/0.97  fof(f62,plain,(
% 2.59/0.97    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 2.59/0.97    inference(nnf_transformation,[],[f17])).
% 2.59/0.97  
% 2.59/0.97  fof(f88,plain,(
% 2.59/0.97    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 2.59/0.97    inference(cnf_transformation,[],[f62])).
% 2.59/0.97  
% 2.59/0.97  fof(f87,plain,(
% 2.59/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 2.59/0.97    inference(cnf_transformation,[],[f62])).
% 2.59/0.97  
% 2.59/0.97  cnf(c_38,negated_conjecture,
% 2.59/0.97      ( r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK3)) ),
% 2.59/0.97      inference(cnf_transformation,[],[f122]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_1224,plain,
% 2.59/0.97      ( r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK3)) = iProver_top ),
% 2.59/0.97      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_36,plain,
% 2.59/0.97      ( ~ r1_tarski(X0,k1_tarski(X1))
% 2.59/0.97      | k1_tarski(X1) = X0
% 2.59/0.97      | k1_xboole_0 = X0 ),
% 2.59/0.97      inference(cnf_transformation,[],[f107]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_1225,plain,
% 2.59/0.97      ( k1_tarski(X0) = X1
% 2.59/0.97      | k1_xboole_0 = X1
% 2.59/0.97      | r1_tarski(X1,k1_tarski(X0)) != iProver_top ),
% 2.59/0.97      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_2826,plain,
% 2.59/0.97      ( k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK3)
% 2.59/0.97      | k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_xboole_0 ),
% 2.59/0.97      inference(superposition,[status(thm)],[c_1224,c_1225]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_37,negated_conjecture,
% 2.59/0.97      ( k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) != k1_tarski(sK3) ),
% 2.59/0.97      inference(cnf_transformation,[],[f121]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_3479,plain,
% 2.59/0.97      ( k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_xboole_0 ),
% 2.59/0.97      inference(global_propositional_subsumption,
% 2.59/0.97                [status(thm)],
% 2.59/0.97                [c_2826,c_37]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_27,plain,
% 2.59/0.97      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 2.59/0.97      inference(cnf_transformation,[],[f93]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_1228,plain,
% 2.59/0.97      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 2.59/0.97      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_3493,plain,
% 2.59/0.97      ( r1_tarski(k1_tarski(sK1),k1_xboole_0) = iProver_top ),
% 2.59/0.97      inference(superposition,[status(thm)],[c_3479,c_1228]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_23,plain,
% 2.59/0.97      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 2.59/0.97      inference(cnf_transformation,[],[f89]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_1231,plain,
% 2.59/0.97      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.59/0.97      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_3753,plain,
% 2.59/0.97      ( k1_tarski(sK1) = k1_xboole_0 ),
% 2.59/0.97      inference(superposition,[status(thm)],[c_3493,c_1231]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_32,plain,
% 2.59/0.97      ( r2_hidden(X0,X1)
% 2.59/0.97      | ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ),
% 2.59/0.97      inference(cnf_transformation,[],[f105]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_33,plain,
% 2.59/0.97      ( ~ r2_hidden(X0,X1)
% 2.59/0.97      | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ),
% 2.59/0.97      inference(cnf_transformation,[],[f106]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_395,plain,
% 2.59/0.97      ( ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
% 2.59/0.97      | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ),
% 2.59/0.97      inference(resolution,[status(thm)],[c_32,c_33]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_1223,plain,
% 2.59/0.97      ( k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
% 2.59/0.97      | r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) != iProver_top ),
% 2.59/0.97      inference(predicate_to_equality,[status(thm)],[c_395]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_6915,plain,
% 2.59/0.97      ( k4_xboole_0(k1_xboole_0,X0) != k1_tarski(sK1)
% 2.59/0.97      | r1_tarski(k2_xboole_0(k1_tarski(sK1),X0),X0) != iProver_top ),
% 2.59/0.97      inference(superposition,[status(thm)],[c_3753,c_1223]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_6918,plain,
% 2.59/0.97      ( k4_xboole_0(k1_xboole_0,X0) != k1_xboole_0
% 2.59/0.97      | r1_tarski(k2_xboole_0(k1_xboole_0,X0),X0) != iProver_top ),
% 2.59/0.97      inference(light_normalisation,[status(thm)],[c_6915,c_3753]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_6922,plain,
% 2.59/0.97      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.59/0.97      | r1_tarski(k2_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 2.59/0.97      inference(instantiation,[status(thm)],[c_6918]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_656,plain,
% 2.59/0.97      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.59/0.97      theory(equality) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_5131,plain,
% 2.59/0.97      ( ~ r1_tarski(X0,X1)
% 2.59/0.97      | r1_tarski(k2_xboole_0(X2,X3),X4)
% 2.59/0.97      | X4 != X1
% 2.59/0.97      | k2_xboole_0(X2,X3) != X0 ),
% 2.59/0.97      inference(instantiation,[status(thm)],[c_656]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_5132,plain,
% 2.59/0.97      ( X0 != X1
% 2.59/0.97      | k2_xboole_0(X2,X3) != X4
% 2.59/0.97      | r1_tarski(X4,X1) != iProver_top
% 2.59/0.97      | r1_tarski(k2_xboole_0(X2,X3),X0) = iProver_top ),
% 2.59/0.97      inference(predicate_to_equality,[status(thm)],[c_5131]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_5134,plain,
% 2.59/0.97      ( k2_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.59/0.97      | k1_xboole_0 != k1_xboole_0
% 2.59/0.97      | r1_tarski(k2_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top
% 2.59/0.97      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.59/0.97      inference(instantiation,[status(thm)],[c_5132]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_9,plain,
% 2.59/0.97      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 2.59/0.97      inference(cnf_transformation,[],[f75]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_102,plain,
% 2.59/0.97      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.59/0.97      | k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.59/0.97      inference(instantiation,[status(thm)],[c_9]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_18,plain,
% 2.59/0.97      ( r1_tarski(k1_xboole_0,X0) ),
% 2.59/0.97      inference(cnf_transformation,[],[f84]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_83,plain,
% 2.59/0.97      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.59/0.97      inference(instantiation,[status(thm)],[c_18]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_21,plain,
% 2.59/0.97      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 2.59/0.97      inference(cnf_transformation,[],[f88]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_74,plain,
% 2.59/0.97      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.59/0.97      | k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.59/0.97      inference(instantiation,[status(thm)],[c_21]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_22,plain,
% 2.59/0.97      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 2.59/0.97      inference(cnf_transformation,[],[f87]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_70,plain,
% 2.59/0.97      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 2.59/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 2.59/0.97      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_72,plain,
% 2.59/0.97      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.59/0.97      | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.59/0.97      inference(instantiation,[status(thm)],[c_70]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(c_68,plain,
% 2.59/0.97      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.59/0.97      | k1_xboole_0 = k1_xboole_0 ),
% 2.59/0.97      inference(instantiation,[status(thm)],[c_23]) ).
% 2.59/0.97  
% 2.59/0.97  cnf(contradiction,plain,
% 2.59/0.97      ( $false ),
% 2.59/0.97      inference(minisat,
% 2.59/0.97                [status(thm)],
% 2.59/0.97                [c_6922,c_5134,c_102,c_83,c_74,c_72,c_68]) ).
% 2.59/0.97  
% 2.59/0.97  
% 2.59/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.59/0.97  
% 2.59/0.97  ------                               Statistics
% 2.59/0.97  
% 2.59/0.97  ------ General
% 2.59/0.97  
% 2.59/0.97  abstr_ref_over_cycles:                  0
% 2.59/0.97  abstr_ref_under_cycles:                 0
% 2.59/0.97  gc_basic_clause_elim:                   0
% 2.59/0.97  forced_gc_time:                         0
% 2.59/0.97  parsing_time:                           0.011
% 2.59/0.97  unif_index_cands_time:                  0.
% 2.59/0.97  unif_index_add_time:                    0.
% 2.59/0.97  orderings_time:                         0.
% 2.59/0.97  out_proof_time:                         0.006
% 2.59/0.97  total_time:                             0.196
% 2.59/0.97  num_of_symbols:                         43
% 2.59/0.97  num_of_terms:                           7618
% 2.59/0.97  
% 2.59/0.97  ------ Preprocessing
% 2.59/0.97  
% 2.59/0.97  num_of_splits:                          0
% 2.59/0.97  num_of_split_atoms:                     0
% 2.59/0.97  num_of_reused_defs:                     0
% 2.59/0.97  num_eq_ax_congr_red:                    41
% 2.59/0.97  num_of_sem_filtered_clauses:            1
% 2.59/0.97  num_of_subtypes:                        0
% 2.59/0.97  monotx_restored_types:                  0
% 2.59/0.97  sat_num_of_epr_types:                   0
% 2.59/0.97  sat_num_of_non_cyclic_types:            0
% 2.59/0.97  sat_guarded_non_collapsed_types:        0
% 2.59/0.97  num_pure_diseq_elim:                    0
% 2.59/0.97  simp_replaced_by:                       0
% 2.59/0.97  res_preprocessed:                       162
% 2.59/0.97  prep_upred:                             0
% 2.59/0.97  prep_unflattend:                        0
% 2.59/0.97  smt_new_axioms:                         0
% 2.59/0.97  pred_elim_cands:                        1
% 2.59/0.97  pred_elim:                              1
% 2.59/0.97  pred_elim_cl:                           1
% 2.59/0.97  pred_elim_cycles:                       3
% 2.59/0.97  merged_defs:                            16
% 2.59/0.97  merged_defs_ncl:                        0
% 2.59/0.97  bin_hyper_res:                          16
% 2.59/0.97  prep_cycles:                            4
% 2.59/0.97  pred_elim_time:                         0.001
% 2.59/0.97  splitting_time:                         0.
% 2.59/0.97  sem_filter_time:                        0.
% 2.59/0.97  monotx_time:                            0.
% 2.59/0.97  subtype_inf_time:                       0.
% 2.59/0.97  
% 2.59/0.97  ------ Problem properties
% 2.59/0.97  
% 2.59/0.97  clauses:                                37
% 2.59/0.97  conjectures:                            2
% 2.59/0.97  epr:                                    4
% 2.59/0.97  horn:                                   34
% 2.59/0.97  ground:                                 2
% 2.59/0.97  unary:                                  18
% 2.59/0.97  binary:                                 13
% 2.59/0.98  lits:                                   65
% 2.59/0.98  lits_eq:                                22
% 2.59/0.98  fd_pure:                                0
% 2.59/0.98  fd_pseudo:                              0
% 2.59/0.98  fd_cond:                                1
% 2.59/0.98  fd_pseudo_cond:                         5
% 2.59/0.98  ac_symbols:                             1
% 2.59/0.98  
% 2.59/0.98  ------ Propositional Solver
% 2.59/0.98  
% 2.59/0.98  prop_solver_calls:                      27
% 2.59/0.98  prop_fast_solver_calls:                 643
% 2.59/0.98  smt_solver_calls:                       0
% 2.59/0.98  smt_fast_solver_calls:                  0
% 2.59/0.98  prop_num_of_clauses:                    2195
% 2.59/0.98  prop_preprocess_simplified:             7344
% 2.59/0.98  prop_fo_subsumed:                       1
% 2.59/0.98  prop_solver_time:                       0.
% 2.59/0.98  smt_solver_time:                        0.
% 2.59/0.98  smt_fast_solver_time:                   0.
% 2.59/0.98  prop_fast_solver_time:                  0.
% 2.59/0.98  prop_unsat_core_time:                   0.
% 2.59/0.98  
% 2.59/0.98  ------ QBF
% 2.59/0.98  
% 2.59/0.98  qbf_q_res:                              0
% 2.59/0.98  qbf_num_tautologies:                    0
% 2.59/0.98  qbf_prep_cycles:                        0
% 2.59/0.98  
% 2.59/0.98  ------ BMC1
% 2.59/0.98  
% 2.59/0.98  bmc1_current_bound:                     -1
% 2.59/0.98  bmc1_last_solved_bound:                 -1
% 2.59/0.98  bmc1_unsat_core_size:                   -1
% 2.59/0.98  bmc1_unsat_core_parents_size:           -1
% 2.59/0.98  bmc1_merge_next_fun:                    0
% 2.59/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.59/0.98  
% 2.59/0.98  ------ Instantiation
% 2.59/0.98  
% 2.59/0.98  inst_num_of_clauses:                    576
% 2.59/0.98  inst_num_in_passive:                    161
% 2.59/0.98  inst_num_in_active:                     222
% 2.59/0.98  inst_num_in_unprocessed:                194
% 2.59/0.98  inst_num_of_loops:                      230
% 2.59/0.98  inst_num_of_learning_restarts:          0
% 2.59/0.98  inst_num_moves_active_passive:          6
% 2.59/0.98  inst_lit_activity:                      0
% 2.59/0.98  inst_lit_activity_moves:                0
% 2.59/0.98  inst_num_tautologies:                   0
% 2.59/0.98  inst_num_prop_implied:                  0
% 2.59/0.98  inst_num_existing_simplified:           0
% 2.59/0.98  inst_num_eq_res_simplified:             0
% 2.59/0.98  inst_num_child_elim:                    0
% 2.59/0.98  inst_num_of_dismatching_blockings:      377
% 2.59/0.98  inst_num_of_non_proper_insts:           437
% 2.59/0.98  inst_num_of_duplicates:                 0
% 2.59/0.98  inst_inst_num_from_inst_to_res:         0
% 2.59/0.98  inst_dismatching_checking_time:         0.
% 2.59/0.98  
% 2.59/0.98  ------ Resolution
% 2.59/0.98  
% 2.59/0.98  res_num_of_clauses:                     0
% 2.59/0.98  res_num_in_passive:                     0
% 2.59/0.98  res_num_in_active:                      0
% 2.59/0.98  res_num_of_loops:                       166
% 2.59/0.98  res_forward_subset_subsumed:            53
% 2.59/0.98  res_backward_subset_subsumed:           4
% 2.59/0.98  res_forward_subsumed:                   0
% 2.59/0.98  res_backward_subsumed:                  0
% 2.59/0.98  res_forward_subsumption_resolution:     0
% 2.59/0.98  res_backward_subsumption_resolution:    0
% 2.59/0.98  res_clause_to_clause_subsumption:       3580
% 2.59/0.98  res_orphan_elimination:                 0
% 2.59/0.98  res_tautology_del:                      41
% 2.59/0.98  res_num_eq_res_simplified:              0
% 2.59/0.98  res_num_sel_changes:                    0
% 2.59/0.98  res_moves_from_active_to_pass:          0
% 2.59/0.98  
% 2.59/0.98  ------ Superposition
% 2.59/0.98  
% 2.59/0.98  sup_time_total:                         0.
% 2.59/0.98  sup_time_generating:                    0.
% 2.59/0.98  sup_time_sim_full:                      0.
% 2.59/0.98  sup_time_sim_immed:                     0.
% 2.59/0.98  
% 2.59/0.98  sup_num_of_clauses:                     240
% 2.59/0.98  sup_num_in_active:                      32
% 2.59/0.98  sup_num_in_passive:                     208
% 2.59/0.98  sup_num_of_loops:                       45
% 2.59/0.98  sup_fw_superposition:                   408
% 2.59/0.98  sup_bw_superposition:                   471
% 2.59/0.98  sup_immediate_simplified:               304
% 2.59/0.98  sup_given_eliminated:                   2
% 2.59/0.98  comparisons_done:                       0
% 2.59/0.98  comparisons_avoided:                    0
% 2.59/0.98  
% 2.59/0.98  ------ Simplifications
% 2.59/0.98  
% 2.59/0.98  
% 2.59/0.98  sim_fw_subset_subsumed:                 1
% 2.59/0.98  sim_bw_subset_subsumed:                 0
% 2.59/0.98  sim_fw_subsumed:                        37
% 2.59/0.98  sim_bw_subsumed:                        0
% 2.59/0.98  sim_fw_subsumption_res:                 0
% 2.59/0.98  sim_bw_subsumption_res:                 0
% 2.59/0.98  sim_tautology_del:                      0
% 2.59/0.98  sim_eq_tautology_del:                   26
% 2.59/0.98  sim_eq_res_simp:                        0
% 2.59/0.98  sim_fw_demodulated:                     116
% 2.59/0.98  sim_bw_demodulated:                     44
% 2.59/0.98  sim_light_normalised:                   147
% 2.59/0.98  sim_joinable_taut:                      46
% 2.59/0.98  sim_joinable_simp:                      0
% 2.59/0.98  sim_ac_normalised:                      0
% 2.59/0.98  sim_smt_subsumption:                    0
% 2.59/0.98  
%------------------------------------------------------------------------------
