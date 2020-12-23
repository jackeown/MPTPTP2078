%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:48:51 EST 2020

% Result     : Theorem 23.06s
% Output     : CNFRefutation 23.06s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 107 expanded)
%              Number of clauses        :   33 (  37 expanded)
%              Number of leaves         :    8 (  25 expanded)
%              Depth                    :   13
%              Number of atoms          :  140 ( 329 expanded)
%              Number of equality atoms :   51 (  55 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
           => r1_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
             => r1_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f68,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
     => ( ~ r1_xboole_0(X0,sK10)
        & r1_xboole_0(k1_relat_1(X0),k1_relat_1(sK10))
        & v1_relat_1(sK10) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_xboole_0(X0,X1)
            & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_xboole_0(sK9,X1)
          & r1_xboole_0(k1_relat_1(sK9),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,
    ( ~ r1_xboole_0(sK9,sK10)
    & r1_xboole_0(k1_relat_1(sK9),k1_relat_1(sK10))
    & v1_relat_1(sK10)
    & v1_relat_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f47,f68,f67])).

fof(f107,plain,(
    r1_xboole_0(k1_relat_1(sK9),k1_relat_1(sK10)) ),
    inference(cnf_transformation,[],[f69])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f105,plain,(
    v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f69])).

fof(f106,plain,(
    v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f69])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f92,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f108,plain,(
    ~ r1_xboole_0(sK9,sK10) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_36,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(sK9),k1_relat_1(sK10)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1516,plain,
    ( r1_xboole_0(k1_relat_1(sK9),k1_relat_1(sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1551,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4637,plain,
    ( k3_xboole_0(k1_relat_1(sK9),k1_relat_1(sK10)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1516,c_1551])).

cnf(c_26,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1526,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6003,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK9,sK10)),k1_xboole_0) = iProver_top
    | v1_relat_1(sK10) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_4637,c_1526])).

cnf(c_38,negated_conjecture,
    ( v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_39,plain,
    ( v1_relat_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_40,plain,
    ( v1_relat_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_112086,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK9,sK10)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6003,c_39,c_40])).

cnf(c_33,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1519,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_112091,plain,
    ( k7_relat_1(k3_xboole_0(sK9,sK10),k1_xboole_0) = k3_xboole_0(sK9,sK10)
    | v1_relat_1(k3_xboole_0(sK9,sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_112086,c_1519])).

cnf(c_1514,plain,
    ( v1_relat_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_21,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1531,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k3_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_22,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1530,plain,
    ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3184,plain,
    ( k7_relat_1(k3_xboole_0(X0,X1),k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1531,c_1530])).

cnf(c_9145,plain,
    ( k7_relat_1(k3_xboole_0(sK9,X0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1514,c_3184])).

cnf(c_112092,plain,
    ( k3_xboole_0(sK9,sK10) = k1_xboole_0
    | v1_relat_1(k3_xboole_0(sK9,sK10)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_112091,c_9145])).

cnf(c_1890,plain,
    ( v1_relat_1(k3_xboole_0(sK9,X0))
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_47037,plain,
    ( v1_relat_1(k3_xboole_0(sK9,sK10))
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_1890])).

cnf(c_47038,plain,
    ( v1_relat_1(k3_xboole_0(sK9,sK10)) = iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47037])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_317,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_35,negated_conjecture,
    ( ~ r1_xboole_0(sK9,sK10) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_616,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | sK10 != X1
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_317,c_35])).

cnf(c_617,plain,
    ( k3_xboole_0(sK9,sK10) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_616])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_112092,c_47038,c_617,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n024.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:45:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 23.06/3.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.06/3.49  
% 23.06/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.06/3.49  
% 23.06/3.49  ------  iProver source info
% 23.06/3.49  
% 23.06/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.06/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.06/3.49  git: non_committed_changes: false
% 23.06/3.49  git: last_make_outside_of_git: false
% 23.06/3.49  
% 23.06/3.49  ------ 
% 23.06/3.49  
% 23.06/3.49  ------ Input Options
% 23.06/3.49  
% 23.06/3.49  --out_options                           all
% 23.06/3.49  --tptp_safe_out                         true
% 23.06/3.49  --problem_path                          ""
% 23.06/3.49  --include_path                          ""
% 23.06/3.49  --clausifier                            res/vclausify_rel
% 23.06/3.49  --clausifier_options                    --mode clausify
% 23.06/3.49  --stdin                                 false
% 23.06/3.49  --stats_out                             all
% 23.06/3.49  
% 23.06/3.49  ------ General Options
% 23.06/3.49  
% 23.06/3.49  --fof                                   false
% 23.06/3.49  --time_out_real                         305.
% 23.06/3.49  --time_out_virtual                      -1.
% 23.06/3.49  --symbol_type_check                     false
% 23.06/3.49  --clausify_out                          false
% 23.06/3.49  --sig_cnt_out                           false
% 23.06/3.49  --trig_cnt_out                          false
% 23.06/3.49  --trig_cnt_out_tolerance                1.
% 23.06/3.49  --trig_cnt_out_sk_spl                   false
% 23.06/3.49  --abstr_cl_out                          false
% 23.06/3.49  
% 23.06/3.49  ------ Global Options
% 23.06/3.49  
% 23.06/3.49  --schedule                              default
% 23.06/3.49  --add_important_lit                     false
% 23.06/3.49  --prop_solver_per_cl                    1000
% 23.06/3.49  --min_unsat_core                        false
% 23.06/3.49  --soft_assumptions                      false
% 23.06/3.49  --soft_lemma_size                       3
% 23.06/3.49  --prop_impl_unit_size                   0
% 23.06/3.49  --prop_impl_unit                        []
% 23.06/3.49  --share_sel_clauses                     true
% 23.06/3.49  --reset_solvers                         false
% 23.06/3.49  --bc_imp_inh                            [conj_cone]
% 23.06/3.49  --conj_cone_tolerance                   3.
% 23.06/3.49  --extra_neg_conj                        none
% 23.06/3.49  --large_theory_mode                     true
% 23.06/3.49  --prolific_symb_bound                   200
% 23.06/3.49  --lt_threshold                          2000
% 23.06/3.49  --clause_weak_htbl                      true
% 23.06/3.49  --gc_record_bc_elim                     false
% 23.06/3.49  
% 23.06/3.49  ------ Preprocessing Options
% 23.06/3.49  
% 23.06/3.49  --preprocessing_flag                    true
% 23.06/3.49  --time_out_prep_mult                    0.1
% 23.06/3.49  --splitting_mode                        input
% 23.06/3.49  --splitting_grd                         true
% 23.06/3.49  --splitting_cvd                         false
% 23.06/3.49  --splitting_cvd_svl                     false
% 23.06/3.49  --splitting_nvd                         32
% 23.06/3.49  --sub_typing                            true
% 23.06/3.49  --prep_gs_sim                           true
% 23.06/3.49  --prep_unflatten                        true
% 23.06/3.49  --prep_res_sim                          true
% 23.06/3.49  --prep_upred                            true
% 23.06/3.49  --prep_sem_filter                       exhaustive
% 23.06/3.49  --prep_sem_filter_out                   false
% 23.06/3.49  --pred_elim                             true
% 23.06/3.49  --res_sim_input                         true
% 23.06/3.49  --eq_ax_congr_red                       true
% 23.06/3.49  --pure_diseq_elim                       true
% 23.06/3.49  --brand_transform                       false
% 23.06/3.49  --non_eq_to_eq                          false
% 23.06/3.49  --prep_def_merge                        true
% 23.06/3.49  --prep_def_merge_prop_impl              false
% 23.06/3.49  --prep_def_merge_mbd                    true
% 23.06/3.49  --prep_def_merge_tr_red                 false
% 23.06/3.49  --prep_def_merge_tr_cl                  false
% 23.06/3.49  --smt_preprocessing                     true
% 23.06/3.49  --smt_ac_axioms                         fast
% 23.06/3.49  --preprocessed_out                      false
% 23.06/3.49  --preprocessed_stats                    false
% 23.06/3.49  
% 23.06/3.49  ------ Abstraction refinement Options
% 23.06/3.49  
% 23.06/3.49  --abstr_ref                             []
% 23.06/3.49  --abstr_ref_prep                        false
% 23.06/3.49  --abstr_ref_until_sat                   false
% 23.06/3.49  --abstr_ref_sig_restrict                funpre
% 23.06/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.06/3.49  --abstr_ref_under                       []
% 23.06/3.49  
% 23.06/3.49  ------ SAT Options
% 23.06/3.49  
% 23.06/3.49  --sat_mode                              false
% 23.06/3.49  --sat_fm_restart_options                ""
% 23.06/3.49  --sat_gr_def                            false
% 23.06/3.49  --sat_epr_types                         true
% 23.06/3.49  --sat_non_cyclic_types                  false
% 23.06/3.49  --sat_finite_models                     false
% 23.06/3.49  --sat_fm_lemmas                         false
% 23.06/3.49  --sat_fm_prep                           false
% 23.06/3.49  --sat_fm_uc_incr                        true
% 23.06/3.49  --sat_out_model                         small
% 23.06/3.49  --sat_out_clauses                       false
% 23.06/3.49  
% 23.06/3.49  ------ QBF Options
% 23.06/3.49  
% 23.06/3.49  --qbf_mode                              false
% 23.06/3.49  --qbf_elim_univ                         false
% 23.06/3.49  --qbf_dom_inst                          none
% 23.06/3.49  --qbf_dom_pre_inst                      false
% 23.06/3.49  --qbf_sk_in                             false
% 23.06/3.49  --qbf_pred_elim                         true
% 23.06/3.49  --qbf_split                             512
% 23.06/3.49  
% 23.06/3.49  ------ BMC1 Options
% 23.06/3.49  
% 23.06/3.49  --bmc1_incremental                      false
% 23.06/3.49  --bmc1_axioms                           reachable_all
% 23.06/3.49  --bmc1_min_bound                        0
% 23.06/3.49  --bmc1_max_bound                        -1
% 23.06/3.49  --bmc1_max_bound_default                -1
% 23.06/3.49  --bmc1_symbol_reachability              true
% 23.06/3.49  --bmc1_property_lemmas                  false
% 23.06/3.49  --bmc1_k_induction                      false
% 23.06/3.49  --bmc1_non_equiv_states                 false
% 23.06/3.49  --bmc1_deadlock                         false
% 23.06/3.49  --bmc1_ucm                              false
% 23.06/3.49  --bmc1_add_unsat_core                   none
% 23.06/3.49  --bmc1_unsat_core_children              false
% 23.06/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.06/3.49  --bmc1_out_stat                         full
% 23.06/3.49  --bmc1_ground_init                      false
% 23.06/3.49  --bmc1_pre_inst_next_state              false
% 23.06/3.49  --bmc1_pre_inst_state                   false
% 23.06/3.49  --bmc1_pre_inst_reach_state             false
% 23.06/3.49  --bmc1_out_unsat_core                   false
% 23.06/3.49  --bmc1_aig_witness_out                  false
% 23.06/3.49  --bmc1_verbose                          false
% 23.06/3.49  --bmc1_dump_clauses_tptp                false
% 23.06/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.06/3.49  --bmc1_dump_file                        -
% 23.06/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.06/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.06/3.49  --bmc1_ucm_extend_mode                  1
% 23.06/3.49  --bmc1_ucm_init_mode                    2
% 23.06/3.49  --bmc1_ucm_cone_mode                    none
% 23.06/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.06/3.49  --bmc1_ucm_relax_model                  4
% 23.06/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.06/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.06/3.49  --bmc1_ucm_layered_model                none
% 23.06/3.49  --bmc1_ucm_max_lemma_size               10
% 23.06/3.49  
% 23.06/3.49  ------ AIG Options
% 23.06/3.49  
% 23.06/3.49  --aig_mode                              false
% 23.06/3.49  
% 23.06/3.49  ------ Instantiation Options
% 23.06/3.49  
% 23.06/3.49  --instantiation_flag                    true
% 23.06/3.49  --inst_sos_flag                         false
% 23.06/3.49  --inst_sos_phase                        true
% 23.06/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.06/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.06/3.49  --inst_lit_sel_side                     num_symb
% 23.06/3.49  --inst_solver_per_active                1400
% 23.06/3.49  --inst_solver_calls_frac                1.
% 23.06/3.49  --inst_passive_queue_type               priority_queues
% 23.06/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.06/3.49  --inst_passive_queues_freq              [25;2]
% 23.06/3.49  --inst_dismatching                      true
% 23.06/3.49  --inst_eager_unprocessed_to_passive     true
% 23.06/3.49  --inst_prop_sim_given                   true
% 23.06/3.49  --inst_prop_sim_new                     false
% 23.06/3.49  --inst_subs_new                         false
% 23.06/3.49  --inst_eq_res_simp                      false
% 23.06/3.49  --inst_subs_given                       false
% 23.06/3.49  --inst_orphan_elimination               true
% 23.06/3.49  --inst_learning_loop_flag               true
% 23.06/3.49  --inst_learning_start                   3000
% 23.06/3.49  --inst_learning_factor                  2
% 23.06/3.49  --inst_start_prop_sim_after_learn       3
% 23.06/3.49  --inst_sel_renew                        solver
% 23.06/3.49  --inst_lit_activity_flag                true
% 23.06/3.49  --inst_restr_to_given                   false
% 23.06/3.49  --inst_activity_threshold               500
% 23.06/3.49  --inst_out_proof                        true
% 23.06/3.49  
% 23.06/3.49  ------ Resolution Options
% 23.06/3.49  
% 23.06/3.49  --resolution_flag                       true
% 23.06/3.49  --res_lit_sel                           adaptive
% 23.06/3.49  --res_lit_sel_side                      none
% 23.06/3.49  --res_ordering                          kbo
% 23.06/3.49  --res_to_prop_solver                    active
% 23.06/3.49  --res_prop_simpl_new                    false
% 23.06/3.49  --res_prop_simpl_given                  true
% 23.06/3.49  --res_passive_queue_type                priority_queues
% 23.06/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.06/3.49  --res_passive_queues_freq               [15;5]
% 23.06/3.49  --res_forward_subs                      full
% 23.06/3.49  --res_backward_subs                     full
% 23.06/3.49  --res_forward_subs_resolution           true
% 23.06/3.49  --res_backward_subs_resolution          true
% 23.06/3.49  --res_orphan_elimination                true
% 23.06/3.49  --res_time_limit                        2.
% 23.06/3.49  --res_out_proof                         true
% 23.06/3.49  
% 23.06/3.49  ------ Superposition Options
% 23.06/3.49  
% 23.06/3.49  --superposition_flag                    true
% 23.06/3.49  --sup_passive_queue_type                priority_queues
% 23.06/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.06/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.06/3.49  --demod_completeness_check              fast
% 23.06/3.49  --demod_use_ground                      true
% 23.06/3.49  --sup_to_prop_solver                    passive
% 23.06/3.49  --sup_prop_simpl_new                    true
% 23.06/3.49  --sup_prop_simpl_given                  true
% 23.06/3.49  --sup_fun_splitting                     false
% 23.06/3.49  --sup_smt_interval                      50000
% 23.06/3.49  
% 23.06/3.49  ------ Superposition Simplification Setup
% 23.06/3.49  
% 23.06/3.49  --sup_indices_passive                   []
% 23.06/3.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.06/3.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.06/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.06/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.06/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.06/3.49  --sup_full_bw                           [BwDemod]
% 23.06/3.49  --sup_immed_triv                        [TrivRules]
% 23.06/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.06/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.06/3.49  --sup_immed_bw_main                     []
% 23.06/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.06/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.06/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.06/3.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.06/3.49  
% 23.06/3.49  ------ Combination Options
% 23.06/3.49  
% 23.06/3.49  --comb_res_mult                         3
% 23.06/3.49  --comb_sup_mult                         2
% 23.06/3.49  --comb_inst_mult                        10
% 23.06/3.49  
% 23.06/3.49  ------ Debug Options
% 23.06/3.49  
% 23.06/3.49  --dbg_backtrace                         false
% 23.06/3.49  --dbg_dump_prop_clauses                 false
% 23.06/3.49  --dbg_dump_prop_clauses_file            -
% 23.06/3.49  --dbg_out_stat                          false
% 23.06/3.49  ------ Parsing...
% 23.06/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.06/3.49  
% 23.06/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 23.06/3.49  
% 23.06/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.06/3.49  
% 23.06/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.06/3.49  ------ Proving...
% 23.06/3.49  ------ Problem Properties 
% 23.06/3.49  
% 23.06/3.49  
% 23.06/3.49  clauses                                 39
% 23.06/3.49  conjectures                             4
% 23.06/3.49  EPR                                     3
% 23.06/3.49  Horn                                    33
% 23.06/3.49  unary                                   4
% 23.06/3.49  binary                                  15
% 23.06/3.49  lits                                    111
% 23.06/3.49  lits eq                                 22
% 23.06/3.49  fd_pure                                 0
% 23.06/3.49  fd_pseudo                               0
% 23.06/3.49  fd_cond                                 0
% 23.06/3.49  fd_pseudo_cond                          6
% 23.06/3.49  AC symbols                              0
% 23.06/3.49  
% 23.06/3.49  ------ Schedule dynamic 5 is on 
% 23.06/3.49  
% 23.06/3.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.06/3.49  
% 23.06/3.49  
% 23.06/3.49  ------ 
% 23.06/3.49  Current options:
% 23.06/3.49  ------ 
% 23.06/3.49  
% 23.06/3.49  ------ Input Options
% 23.06/3.49  
% 23.06/3.49  --out_options                           all
% 23.06/3.49  --tptp_safe_out                         true
% 23.06/3.49  --problem_path                          ""
% 23.06/3.49  --include_path                          ""
% 23.06/3.49  --clausifier                            res/vclausify_rel
% 23.06/3.49  --clausifier_options                    --mode clausify
% 23.06/3.49  --stdin                                 false
% 23.06/3.49  --stats_out                             all
% 23.06/3.49  
% 23.06/3.49  ------ General Options
% 23.06/3.49  
% 23.06/3.49  --fof                                   false
% 23.06/3.49  --time_out_real                         305.
% 23.06/3.49  --time_out_virtual                      -1.
% 23.06/3.49  --symbol_type_check                     false
% 23.06/3.49  --clausify_out                          false
% 23.06/3.49  --sig_cnt_out                           false
% 23.06/3.49  --trig_cnt_out                          false
% 23.06/3.49  --trig_cnt_out_tolerance                1.
% 23.06/3.49  --trig_cnt_out_sk_spl                   false
% 23.06/3.49  --abstr_cl_out                          false
% 23.06/3.49  
% 23.06/3.49  ------ Global Options
% 23.06/3.49  
% 23.06/3.49  --schedule                              default
% 23.06/3.49  --add_important_lit                     false
% 23.06/3.49  --prop_solver_per_cl                    1000
% 23.06/3.49  --min_unsat_core                        false
% 23.06/3.49  --soft_assumptions                      false
% 23.06/3.49  --soft_lemma_size                       3
% 23.06/3.49  --prop_impl_unit_size                   0
% 23.06/3.49  --prop_impl_unit                        []
% 23.06/3.49  --share_sel_clauses                     true
% 23.06/3.49  --reset_solvers                         false
% 23.06/3.49  --bc_imp_inh                            [conj_cone]
% 23.06/3.49  --conj_cone_tolerance                   3.
% 23.06/3.49  --extra_neg_conj                        none
% 23.06/3.49  --large_theory_mode                     true
% 23.06/3.49  --prolific_symb_bound                   200
% 23.06/3.49  --lt_threshold                          2000
% 23.06/3.49  --clause_weak_htbl                      true
% 23.06/3.49  --gc_record_bc_elim                     false
% 23.06/3.49  
% 23.06/3.49  ------ Preprocessing Options
% 23.06/3.49  
% 23.06/3.49  --preprocessing_flag                    true
% 23.06/3.49  --time_out_prep_mult                    0.1
% 23.06/3.49  --splitting_mode                        input
% 23.06/3.49  --splitting_grd                         true
% 23.06/3.49  --splitting_cvd                         false
% 23.06/3.49  --splitting_cvd_svl                     false
% 23.06/3.49  --splitting_nvd                         32
% 23.06/3.49  --sub_typing                            true
% 23.06/3.49  --prep_gs_sim                           true
% 23.06/3.49  --prep_unflatten                        true
% 23.06/3.49  --prep_res_sim                          true
% 23.06/3.49  --prep_upred                            true
% 23.06/3.49  --prep_sem_filter                       exhaustive
% 23.06/3.49  --prep_sem_filter_out                   false
% 23.06/3.49  --pred_elim                             true
% 23.06/3.49  --res_sim_input                         true
% 23.06/3.49  --eq_ax_congr_red                       true
% 23.06/3.49  --pure_diseq_elim                       true
% 23.06/3.49  --brand_transform                       false
% 23.06/3.49  --non_eq_to_eq                          false
% 23.06/3.49  --prep_def_merge                        true
% 23.06/3.49  --prep_def_merge_prop_impl              false
% 23.06/3.49  --prep_def_merge_mbd                    true
% 23.06/3.49  --prep_def_merge_tr_red                 false
% 23.06/3.49  --prep_def_merge_tr_cl                  false
% 23.06/3.49  --smt_preprocessing                     true
% 23.06/3.49  --smt_ac_axioms                         fast
% 23.06/3.49  --preprocessed_out                      false
% 23.06/3.49  --preprocessed_stats                    false
% 23.06/3.49  
% 23.06/3.49  ------ Abstraction refinement Options
% 23.06/3.49  
% 23.06/3.49  --abstr_ref                             []
% 23.06/3.49  --abstr_ref_prep                        false
% 23.06/3.49  --abstr_ref_until_sat                   false
% 23.06/3.49  --abstr_ref_sig_restrict                funpre
% 23.06/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.06/3.49  --abstr_ref_under                       []
% 23.06/3.49  
% 23.06/3.49  ------ SAT Options
% 23.06/3.49  
% 23.06/3.49  --sat_mode                              false
% 23.06/3.49  --sat_fm_restart_options                ""
% 23.06/3.49  --sat_gr_def                            false
% 23.06/3.49  --sat_epr_types                         true
% 23.06/3.49  --sat_non_cyclic_types                  false
% 23.06/3.49  --sat_finite_models                     false
% 23.06/3.49  --sat_fm_lemmas                         false
% 23.06/3.49  --sat_fm_prep                           false
% 23.06/3.49  --sat_fm_uc_incr                        true
% 23.06/3.49  --sat_out_model                         small
% 23.06/3.49  --sat_out_clauses                       false
% 23.06/3.49  
% 23.06/3.49  ------ QBF Options
% 23.06/3.49  
% 23.06/3.49  --qbf_mode                              false
% 23.06/3.49  --qbf_elim_univ                         false
% 23.06/3.49  --qbf_dom_inst                          none
% 23.06/3.49  --qbf_dom_pre_inst                      false
% 23.06/3.49  --qbf_sk_in                             false
% 23.06/3.49  --qbf_pred_elim                         true
% 23.06/3.49  --qbf_split                             512
% 23.06/3.49  
% 23.06/3.49  ------ BMC1 Options
% 23.06/3.49  
% 23.06/3.49  --bmc1_incremental                      false
% 23.06/3.49  --bmc1_axioms                           reachable_all
% 23.06/3.49  --bmc1_min_bound                        0
% 23.06/3.49  --bmc1_max_bound                        -1
% 23.06/3.49  --bmc1_max_bound_default                -1
% 23.06/3.49  --bmc1_symbol_reachability              true
% 23.06/3.49  --bmc1_property_lemmas                  false
% 23.06/3.49  --bmc1_k_induction                      false
% 23.06/3.49  --bmc1_non_equiv_states                 false
% 23.06/3.49  --bmc1_deadlock                         false
% 23.06/3.49  --bmc1_ucm                              false
% 23.06/3.49  --bmc1_add_unsat_core                   none
% 23.06/3.49  --bmc1_unsat_core_children              false
% 23.06/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.06/3.49  --bmc1_out_stat                         full
% 23.06/3.49  --bmc1_ground_init                      false
% 23.06/3.49  --bmc1_pre_inst_next_state              false
% 23.06/3.49  --bmc1_pre_inst_state                   false
% 23.06/3.49  --bmc1_pre_inst_reach_state             false
% 23.06/3.49  --bmc1_out_unsat_core                   false
% 23.06/3.49  --bmc1_aig_witness_out                  false
% 23.06/3.49  --bmc1_verbose                          false
% 23.06/3.49  --bmc1_dump_clauses_tptp                false
% 23.06/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.06/3.49  --bmc1_dump_file                        -
% 23.06/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.06/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.06/3.49  --bmc1_ucm_extend_mode                  1
% 23.06/3.49  --bmc1_ucm_init_mode                    2
% 23.06/3.49  --bmc1_ucm_cone_mode                    none
% 23.06/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.06/3.49  --bmc1_ucm_relax_model                  4
% 23.06/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.06/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.06/3.49  --bmc1_ucm_layered_model                none
% 23.06/3.49  --bmc1_ucm_max_lemma_size               10
% 23.06/3.49  
% 23.06/3.49  ------ AIG Options
% 23.06/3.49  
% 23.06/3.49  --aig_mode                              false
% 23.06/3.49  
% 23.06/3.49  ------ Instantiation Options
% 23.06/3.49  
% 23.06/3.49  --instantiation_flag                    true
% 23.06/3.49  --inst_sos_flag                         false
% 23.06/3.49  --inst_sos_phase                        true
% 23.06/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.06/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.06/3.49  --inst_lit_sel_side                     none
% 23.06/3.49  --inst_solver_per_active                1400
% 23.06/3.49  --inst_solver_calls_frac                1.
% 23.06/3.49  --inst_passive_queue_type               priority_queues
% 23.06/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.06/3.49  --inst_passive_queues_freq              [25;2]
% 23.06/3.49  --inst_dismatching                      true
% 23.06/3.49  --inst_eager_unprocessed_to_passive     true
% 23.06/3.49  --inst_prop_sim_given                   true
% 23.06/3.49  --inst_prop_sim_new                     false
% 23.06/3.49  --inst_subs_new                         false
% 23.06/3.49  --inst_eq_res_simp                      false
% 23.06/3.49  --inst_subs_given                       false
% 23.06/3.49  --inst_orphan_elimination               true
% 23.06/3.49  --inst_learning_loop_flag               true
% 23.06/3.49  --inst_learning_start                   3000
% 23.06/3.49  --inst_learning_factor                  2
% 23.06/3.49  --inst_start_prop_sim_after_learn       3
% 23.06/3.49  --inst_sel_renew                        solver
% 23.06/3.49  --inst_lit_activity_flag                true
% 23.06/3.49  --inst_restr_to_given                   false
% 23.06/3.49  --inst_activity_threshold               500
% 23.06/3.49  --inst_out_proof                        true
% 23.06/3.49  
% 23.06/3.49  ------ Resolution Options
% 23.06/3.49  
% 23.06/3.49  --resolution_flag                       false
% 23.06/3.49  --res_lit_sel                           adaptive
% 23.06/3.49  --res_lit_sel_side                      none
% 23.06/3.49  --res_ordering                          kbo
% 23.06/3.49  --res_to_prop_solver                    active
% 23.06/3.49  --res_prop_simpl_new                    false
% 23.06/3.49  --res_prop_simpl_given                  true
% 23.06/3.49  --res_passive_queue_type                priority_queues
% 23.06/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.06/3.49  --res_passive_queues_freq               [15;5]
% 23.06/3.49  --res_forward_subs                      full
% 23.06/3.49  --res_backward_subs                     full
% 23.06/3.49  --res_forward_subs_resolution           true
% 23.06/3.49  --res_backward_subs_resolution          true
% 23.06/3.49  --res_orphan_elimination                true
% 23.06/3.49  --res_time_limit                        2.
% 23.06/3.49  --res_out_proof                         true
% 23.06/3.49  
% 23.06/3.49  ------ Superposition Options
% 23.06/3.49  
% 23.06/3.49  --superposition_flag                    true
% 23.06/3.49  --sup_passive_queue_type                priority_queues
% 23.06/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.06/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.06/3.49  --demod_completeness_check              fast
% 23.06/3.49  --demod_use_ground                      true
% 23.06/3.49  --sup_to_prop_solver                    passive
% 23.06/3.49  --sup_prop_simpl_new                    true
% 23.06/3.49  --sup_prop_simpl_given                  true
% 23.06/3.49  --sup_fun_splitting                     false
% 23.06/3.49  --sup_smt_interval                      50000
% 23.06/3.49  
% 23.06/3.49  ------ Superposition Simplification Setup
% 23.06/3.49  
% 23.06/3.49  --sup_indices_passive                   []
% 23.06/3.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.06/3.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.06/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.06/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.06/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.06/3.49  --sup_full_bw                           [BwDemod]
% 23.06/3.49  --sup_immed_triv                        [TrivRules]
% 23.06/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.06/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.06/3.49  --sup_immed_bw_main                     []
% 23.06/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.06/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.06/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.06/3.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.06/3.49  
% 23.06/3.49  ------ Combination Options
% 23.06/3.49  
% 23.06/3.49  --comb_res_mult                         3
% 23.06/3.49  --comb_sup_mult                         2
% 23.06/3.49  --comb_inst_mult                        10
% 23.06/3.49  
% 23.06/3.49  ------ Debug Options
% 23.06/3.49  
% 23.06/3.49  --dbg_backtrace                         false
% 23.06/3.49  --dbg_dump_prop_clauses                 false
% 23.06/3.49  --dbg_dump_prop_clauses_file            -
% 23.06/3.49  --dbg_out_stat                          false
% 23.06/3.49  
% 23.06/3.49  
% 23.06/3.49  
% 23.06/3.49  
% 23.06/3.49  ------ Proving...
% 23.06/3.49  
% 23.06/3.49  
% 23.06/3.49  % SZS status Theorem for theBenchmark.p
% 23.06/3.49  
% 23.06/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 23.06/3.49  
% 23.06/3.49  fof(f21,conjecture,(
% 23.06/3.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 23.06/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.06/3.49  
% 23.06/3.49  fof(f22,negated_conjecture,(
% 23.06/3.49    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 23.06/3.49    inference(negated_conjecture,[],[f21])).
% 23.06/3.49  
% 23.06/3.49  fof(f46,plain,(
% 23.06/3.49    ? [X0] : (? [X1] : ((~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 23.06/3.49    inference(ennf_transformation,[],[f22])).
% 23.06/3.49  
% 23.06/3.49  fof(f47,plain,(
% 23.06/3.49    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 23.06/3.49    inference(flattening,[],[f46])).
% 23.06/3.49  
% 23.06/3.49  fof(f68,plain,(
% 23.06/3.49    ( ! [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_xboole_0(X0,sK10) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(sK10)) & v1_relat_1(sK10))) )),
% 23.06/3.49    introduced(choice_axiom,[])).
% 23.06/3.49  
% 23.06/3.49  fof(f67,plain,(
% 23.06/3.49    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_xboole_0(sK9,X1) & r1_xboole_0(k1_relat_1(sK9),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK9))),
% 23.06/3.49    introduced(choice_axiom,[])).
% 23.06/3.49  
% 23.06/3.49  fof(f69,plain,(
% 23.06/3.49    (~r1_xboole_0(sK9,sK10) & r1_xboole_0(k1_relat_1(sK9),k1_relat_1(sK10)) & v1_relat_1(sK10)) & v1_relat_1(sK9)),
% 23.06/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f47,f68,f67])).
% 23.06/3.49  
% 23.06/3.49  fof(f107,plain,(
% 23.06/3.49    r1_xboole_0(k1_relat_1(sK9),k1_relat_1(sK10))),
% 23.06/3.49    inference(cnf_transformation,[],[f69])).
% 23.06/3.49  
% 23.06/3.49  fof(f1,axiom,(
% 23.06/3.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 23.06/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.06/3.49  
% 23.06/3.49  fof(f48,plain,(
% 23.06/3.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 23.06/3.49    inference(nnf_transformation,[],[f1])).
% 23.06/3.49  
% 23.06/3.49  fof(f70,plain,(
% 23.06/3.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 23.06/3.49    inference(cnf_transformation,[],[f48])).
% 23.06/3.49  
% 23.06/3.49  fof(f13,axiom,(
% 23.06/3.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 23.06/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.06/3.49  
% 23.06/3.49  fof(f36,plain,(
% 23.06/3.49    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 23.06/3.49    inference(ennf_transformation,[],[f13])).
% 23.06/3.49  
% 23.06/3.49  fof(f96,plain,(
% 23.06/3.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 23.06/3.49    inference(cnf_transformation,[],[f36])).
% 23.06/3.49  
% 23.06/3.49  fof(f105,plain,(
% 23.06/3.49    v1_relat_1(sK9)),
% 23.06/3.49    inference(cnf_transformation,[],[f69])).
% 23.06/3.49  
% 23.06/3.49  fof(f106,plain,(
% 23.06/3.49    v1_relat_1(sK10)),
% 23.06/3.49    inference(cnf_transformation,[],[f69])).
% 23.06/3.49  
% 23.06/3.49  fof(f19,axiom,(
% 23.06/3.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 23.06/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.06/3.49  
% 23.06/3.49  fof(f43,plain,(
% 23.06/3.49    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 23.06/3.49    inference(ennf_transformation,[],[f19])).
% 23.06/3.49  
% 23.06/3.49  fof(f44,plain,(
% 23.06/3.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 23.06/3.49    inference(flattening,[],[f43])).
% 23.06/3.49  
% 23.06/3.49  fof(f103,plain,(
% 23.06/3.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 23.06/3.49    inference(cnf_transformation,[],[f44])).
% 23.06/3.49  
% 23.06/3.49  fof(f8,axiom,(
% 23.06/3.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 23.06/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.06/3.49  
% 23.06/3.49  fof(f31,plain,(
% 23.06/3.49    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 23.06/3.49    inference(ennf_transformation,[],[f8])).
% 23.06/3.49  
% 23.06/3.49  fof(f91,plain,(
% 23.06/3.49    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 23.06/3.49    inference(cnf_transformation,[],[f31])).
% 23.06/3.49  
% 23.06/3.49  fof(f9,axiom,(
% 23.06/3.49    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 23.06/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.06/3.49  
% 23.06/3.49  fof(f32,plain,(
% 23.06/3.49    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 23.06/3.49    inference(ennf_transformation,[],[f9])).
% 23.06/3.49  
% 23.06/3.49  fof(f92,plain,(
% 23.06/3.49    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 23.06/3.49    inference(cnf_transformation,[],[f32])).
% 23.06/3.49  
% 23.06/3.49  fof(f71,plain,(
% 23.06/3.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 23.06/3.49    inference(cnf_transformation,[],[f48])).
% 23.06/3.49  
% 23.06/3.49  fof(f108,plain,(
% 23.06/3.49    ~r1_xboole_0(sK9,sK10)),
% 23.06/3.49    inference(cnf_transformation,[],[f69])).
% 23.06/3.49  
% 23.06/3.49  cnf(c_36,negated_conjecture,
% 23.06/3.49      ( r1_xboole_0(k1_relat_1(sK9),k1_relat_1(sK10)) ),
% 23.06/3.49      inference(cnf_transformation,[],[f107]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_1516,plain,
% 23.06/3.49      ( r1_xboole_0(k1_relat_1(sK9),k1_relat_1(sK10)) = iProver_top ),
% 23.06/3.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_1,plain,
% 23.06/3.49      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 23.06/3.49      inference(cnf_transformation,[],[f70]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_1551,plain,
% 23.06/3.49      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 23.06/3.49      | r1_xboole_0(X0,X1) != iProver_top ),
% 23.06/3.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_4637,plain,
% 23.06/3.49      ( k3_xboole_0(k1_relat_1(sK9),k1_relat_1(sK10)) = k1_xboole_0 ),
% 23.06/3.49      inference(superposition,[status(thm)],[c_1516,c_1551]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_26,plain,
% 23.06/3.49      ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
% 23.06/3.49      | ~ v1_relat_1(X1)
% 23.06/3.49      | ~ v1_relat_1(X0) ),
% 23.06/3.49      inference(cnf_transformation,[],[f96]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_1526,plain,
% 23.06/3.49      ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) = iProver_top
% 23.06/3.49      | v1_relat_1(X0) != iProver_top
% 23.06/3.49      | v1_relat_1(X1) != iProver_top ),
% 23.06/3.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_6003,plain,
% 23.06/3.49      ( r1_tarski(k1_relat_1(k3_xboole_0(sK9,sK10)),k1_xboole_0) = iProver_top
% 23.06/3.49      | v1_relat_1(sK10) != iProver_top
% 23.06/3.49      | v1_relat_1(sK9) != iProver_top ),
% 23.06/3.49      inference(superposition,[status(thm)],[c_4637,c_1526]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_38,negated_conjecture,
% 23.06/3.49      ( v1_relat_1(sK9) ),
% 23.06/3.49      inference(cnf_transformation,[],[f105]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_39,plain,
% 23.06/3.49      ( v1_relat_1(sK9) = iProver_top ),
% 23.06/3.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_37,negated_conjecture,
% 23.06/3.49      ( v1_relat_1(sK10) ),
% 23.06/3.49      inference(cnf_transformation,[],[f106]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_40,plain,
% 23.06/3.49      ( v1_relat_1(sK10) = iProver_top ),
% 23.06/3.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_112086,plain,
% 23.06/3.49      ( r1_tarski(k1_relat_1(k3_xboole_0(sK9,sK10)),k1_xboole_0) = iProver_top ),
% 23.06/3.49      inference(global_propositional_subsumption,
% 23.06/3.49                [status(thm)],
% 23.06/3.49                [c_6003,c_39,c_40]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_33,plain,
% 23.06/3.49      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 23.06/3.49      | ~ v1_relat_1(X0)
% 23.06/3.49      | k7_relat_1(X0,X1) = X0 ),
% 23.06/3.49      inference(cnf_transformation,[],[f103]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_1519,plain,
% 23.06/3.49      ( k7_relat_1(X0,X1) = X0
% 23.06/3.49      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 23.06/3.49      | v1_relat_1(X0) != iProver_top ),
% 23.06/3.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_112091,plain,
% 23.06/3.49      ( k7_relat_1(k3_xboole_0(sK9,sK10),k1_xboole_0) = k3_xboole_0(sK9,sK10)
% 23.06/3.49      | v1_relat_1(k3_xboole_0(sK9,sK10)) != iProver_top ),
% 23.06/3.49      inference(superposition,[status(thm)],[c_112086,c_1519]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_1514,plain,
% 23.06/3.49      ( v1_relat_1(sK9) = iProver_top ),
% 23.06/3.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_21,plain,
% 23.06/3.49      ( ~ v1_relat_1(X0) | v1_relat_1(k3_xboole_0(X0,X1)) ),
% 23.06/3.49      inference(cnf_transformation,[],[f91]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_1531,plain,
% 23.06/3.49      ( v1_relat_1(X0) != iProver_top
% 23.06/3.49      | v1_relat_1(k3_xboole_0(X0,X1)) = iProver_top ),
% 23.06/3.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_22,plain,
% 23.06/3.49      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 23.06/3.49      inference(cnf_transformation,[],[f92]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_1530,plain,
% 23.06/3.49      ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 23.06/3.49      | v1_relat_1(X0) != iProver_top ),
% 23.06/3.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_3184,plain,
% 23.06/3.49      ( k7_relat_1(k3_xboole_0(X0,X1),k1_xboole_0) = k1_xboole_0
% 23.06/3.49      | v1_relat_1(X0) != iProver_top ),
% 23.06/3.49      inference(superposition,[status(thm)],[c_1531,c_1530]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_9145,plain,
% 23.06/3.49      ( k7_relat_1(k3_xboole_0(sK9,X0),k1_xboole_0) = k1_xboole_0 ),
% 23.06/3.49      inference(superposition,[status(thm)],[c_1514,c_3184]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_112092,plain,
% 23.06/3.49      ( k3_xboole_0(sK9,sK10) = k1_xboole_0
% 23.06/3.49      | v1_relat_1(k3_xboole_0(sK9,sK10)) != iProver_top ),
% 23.06/3.49      inference(demodulation,[status(thm)],[c_112091,c_9145]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_1890,plain,
% 23.06/3.49      ( v1_relat_1(k3_xboole_0(sK9,X0)) | ~ v1_relat_1(sK9) ),
% 23.06/3.49      inference(instantiation,[status(thm)],[c_21]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_47037,plain,
% 23.06/3.49      ( v1_relat_1(k3_xboole_0(sK9,sK10)) | ~ v1_relat_1(sK9) ),
% 23.06/3.49      inference(instantiation,[status(thm)],[c_1890]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_47038,plain,
% 23.06/3.49      ( v1_relat_1(k3_xboole_0(sK9,sK10)) = iProver_top
% 23.06/3.49      | v1_relat_1(sK9) != iProver_top ),
% 23.06/3.49      inference(predicate_to_equality,[status(thm)],[c_47037]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_0,plain,
% 23.06/3.49      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 23.06/3.49      inference(cnf_transformation,[],[f71]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_317,plain,
% 23.06/3.49      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 23.06/3.49      inference(prop_impl,[status(thm)],[c_0]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_35,negated_conjecture,
% 23.06/3.49      ( ~ r1_xboole_0(sK9,sK10) ),
% 23.06/3.49      inference(cnf_transformation,[],[f108]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_616,plain,
% 23.06/3.49      ( k3_xboole_0(X0,X1) != k1_xboole_0 | sK10 != X1 | sK9 != X0 ),
% 23.06/3.49      inference(resolution_lifted,[status(thm)],[c_317,c_35]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(c_617,plain,
% 23.06/3.49      ( k3_xboole_0(sK9,sK10) != k1_xboole_0 ),
% 23.06/3.49      inference(unflattening,[status(thm)],[c_616]) ).
% 23.06/3.49  
% 23.06/3.49  cnf(contradiction,plain,
% 23.06/3.49      ( $false ),
% 23.06/3.49      inference(minisat,[status(thm)],[c_112092,c_47038,c_617,c_39]) ).
% 23.06/3.49  
% 23.06/3.49  
% 23.06/3.49  % SZS output end CNFRefutation for theBenchmark.p
% 23.06/3.49  
% 23.06/3.49  ------                               Statistics
% 23.06/3.49  
% 23.06/3.49  ------ General
% 23.06/3.49  
% 23.06/3.49  abstr_ref_over_cycles:                  0
% 23.06/3.49  abstr_ref_under_cycles:                 0
% 23.06/3.49  gc_basic_clause_elim:                   0
% 23.06/3.49  forced_gc_time:                         0
% 23.06/3.49  parsing_time:                           0.013
% 23.06/3.49  unif_index_cands_time:                  0.
% 23.06/3.49  unif_index_add_time:                    0.
% 23.06/3.49  orderings_time:                         0.
% 23.06/3.49  out_proof_time:                         0.022
% 23.06/3.49  total_time:                             2.907
% 23.06/3.49  num_of_symbols:                         55
% 23.06/3.49  num_of_terms:                           169813
% 23.06/3.49  
% 23.06/3.49  ------ Preprocessing
% 23.06/3.49  
% 23.06/3.49  num_of_splits:                          0
% 23.06/3.49  num_of_split_atoms:                     0
% 23.06/3.49  num_of_reused_defs:                     0
% 23.06/3.49  num_eq_ax_congr_red:                    44
% 23.06/3.49  num_of_sem_filtered_clauses:            1
% 23.06/3.49  num_of_subtypes:                        0
% 23.06/3.49  monotx_restored_types:                  0
% 23.06/3.49  sat_num_of_epr_types:                   0
% 23.06/3.49  sat_num_of_non_cyclic_types:            0
% 23.06/3.49  sat_guarded_non_collapsed_types:        0
% 23.06/3.49  num_pure_diseq_elim:                    0
% 23.06/3.49  simp_replaced_by:                       0
% 23.06/3.49  res_preprocessed:                       146
% 23.06/3.49  prep_upred:                             0
% 23.06/3.49  prep_unflattend:                        15
% 23.06/3.49  smt_new_axioms:                         0
% 23.06/3.49  pred_elim_cands:                        4
% 23.06/3.49  pred_elim:                              0
% 23.06/3.49  pred_elim_cl:                           0
% 23.06/3.49  pred_elim_cycles:                       2
% 23.06/3.49  merged_defs:                            6
% 23.06/3.49  merged_defs_ncl:                        0
% 23.06/3.49  bin_hyper_res:                          6
% 23.06/3.49  prep_cycles:                            3
% 23.06/3.49  pred_elim_time:                         0.003
% 23.06/3.49  splitting_time:                         0.
% 23.06/3.49  sem_filter_time:                        0.
% 23.06/3.49  monotx_time:                            0.001
% 23.06/3.49  subtype_inf_time:                       0.
% 23.06/3.49  
% 23.06/3.49  ------ Problem properties
% 23.06/3.49  
% 23.06/3.49  clauses:                                39
% 23.06/3.49  conjectures:                            4
% 23.06/3.49  epr:                                    3
% 23.06/3.49  horn:                                   33
% 23.06/3.49  ground:                                 4
% 23.06/3.49  unary:                                  4
% 23.06/3.49  binary:                                 15
% 23.06/3.49  lits:                                   111
% 23.06/3.49  lits_eq:                                22
% 23.06/3.49  fd_pure:                                0
% 23.06/3.49  fd_pseudo:                              0
% 23.06/3.49  fd_cond:                                0
% 23.06/3.49  fd_pseudo_cond:                         6
% 23.06/3.49  ac_symbols:                             0
% 23.06/3.49  
% 23.06/3.49  ------ Propositional Solver
% 23.06/3.49  
% 23.06/3.49  prop_solver_calls:                      45
% 23.06/3.49  prop_fast_solver_calls:                 1939
% 23.06/3.49  smt_solver_calls:                       0
% 23.06/3.49  smt_fast_solver_calls:                  0
% 23.06/3.49  prop_num_of_clauses:                    44794
% 23.06/3.49  prop_preprocess_simplified:             69472
% 23.06/3.49  prop_fo_subsumed:                       18
% 23.06/3.49  prop_solver_time:                       0.
% 23.06/3.49  smt_solver_time:                        0.
% 23.06/3.49  smt_fast_solver_time:                   0.
% 23.06/3.49  prop_fast_solver_time:                  0.
% 23.06/3.49  prop_unsat_core_time:                   0.004
% 23.06/3.49  
% 23.06/3.49  ------ QBF
% 23.06/3.49  
% 23.06/3.49  qbf_q_res:                              0
% 23.06/3.49  qbf_num_tautologies:                    0
% 23.06/3.49  qbf_prep_cycles:                        0
% 23.06/3.49  
% 23.06/3.49  ------ BMC1
% 23.06/3.49  
% 23.06/3.49  bmc1_current_bound:                     -1
% 23.06/3.49  bmc1_last_solved_bound:                 -1
% 23.06/3.49  bmc1_unsat_core_size:                   -1
% 23.06/3.49  bmc1_unsat_core_parents_size:           -1
% 23.06/3.49  bmc1_merge_next_fun:                    0
% 23.06/3.49  bmc1_unsat_core_clauses_time:           0.
% 23.06/3.49  
% 23.06/3.49  ------ Instantiation
% 23.06/3.49  
% 23.06/3.49  inst_num_of_clauses:                    1193
% 23.06/3.49  inst_num_in_passive:                    416
% 23.06/3.49  inst_num_in_active:                     2773
% 23.06/3.49  inst_num_in_unprocessed:                263
% 23.06/3.49  inst_num_of_loops:                      3609
% 23.06/3.49  inst_num_of_learning_restarts:          1
% 23.06/3.49  inst_num_moves_active_passive:          834
% 23.06/3.49  inst_lit_activity:                      0
% 23.06/3.49  inst_lit_activity_moves:                1
% 23.06/3.49  inst_num_tautologies:                   0
% 23.06/3.49  inst_num_prop_implied:                  0
% 23.06/3.49  inst_num_existing_simplified:           0
% 23.06/3.49  inst_num_eq_res_simplified:             0
% 23.06/3.49  inst_num_child_elim:                    0
% 23.06/3.49  inst_num_of_dismatching_blockings:      15415
% 23.06/3.49  inst_num_of_non_proper_insts:           6137
% 23.06/3.49  inst_num_of_duplicates:                 0
% 23.06/3.49  inst_inst_num_from_inst_to_res:         0
% 23.06/3.49  inst_dismatching_checking_time:         0.
% 23.06/3.49  
% 23.06/3.49  ------ Resolution
% 23.06/3.49  
% 23.06/3.49  res_num_of_clauses:                     53
% 23.06/3.49  res_num_in_passive:                     53
% 23.06/3.49  res_num_in_active:                      0
% 23.06/3.49  res_num_of_loops:                       149
% 23.06/3.49  res_forward_subset_subsumed:            101
% 23.06/3.49  res_backward_subset_subsumed:           0
% 23.06/3.49  res_forward_subsumed:                   0
% 23.06/3.49  res_backward_subsumed:                  0
% 23.06/3.49  res_forward_subsumption_resolution:     0
% 23.06/3.49  res_backward_subsumption_resolution:    0
% 23.06/3.49  res_clause_to_clause_subsumption:       12758
% 23.06/3.49  res_orphan_elimination:                 0
% 23.06/3.49  res_tautology_del:                      166
% 23.06/3.49  res_num_eq_res_simplified:              0
% 23.06/3.49  res_num_sel_changes:                    0
% 23.06/3.49  res_moves_from_active_to_pass:          0
% 23.06/3.49  
% 23.06/3.49  ------ Superposition
% 23.06/3.49  
% 23.06/3.49  sup_time_total:                         0.
% 23.06/3.49  sup_time_generating:                    0.
% 23.06/3.49  sup_time_sim_full:                      0.
% 23.06/3.49  sup_time_sim_immed:                     0.
% 23.06/3.49  
% 23.06/3.49  sup_num_of_clauses:                     4380
% 23.06/3.49  sup_num_in_active:                      706
% 23.06/3.49  sup_num_in_passive:                     3674
% 23.06/3.49  sup_num_of_loops:                       720
% 23.06/3.49  sup_fw_superposition:                   4145
% 23.06/3.49  sup_bw_superposition:                   1908
% 23.06/3.49  sup_immediate_simplified:               1147
% 23.06/3.49  sup_given_eliminated:                   3
% 23.06/3.49  comparisons_done:                       0
% 23.06/3.49  comparisons_avoided:                    0
% 23.06/3.49  
% 23.06/3.49  ------ Simplifications
% 23.06/3.49  
% 23.06/3.49  
% 23.06/3.49  sim_fw_subset_subsumed:                 172
% 23.06/3.49  sim_bw_subset_subsumed:                 6
% 23.06/3.49  sim_fw_subsumed:                        59
% 23.06/3.49  sim_bw_subsumed:                        1
% 23.06/3.49  sim_fw_subsumption_res:                 25
% 23.06/3.49  sim_bw_subsumption_res:                 0
% 23.06/3.49  sim_tautology_del:                      141
% 23.06/3.49  sim_eq_tautology_del:                   335
% 23.06/3.49  sim_eq_res_simp:                        1
% 23.06/3.49  sim_fw_demodulated:                     52
% 23.06/3.49  sim_bw_demodulated:                     19
% 23.06/3.49  sim_light_normalised:                   855
% 23.06/3.49  sim_joinable_taut:                      0
% 23.06/3.49  sim_joinable_simp:                      0
% 23.06/3.49  sim_ac_normalised:                      0
% 23.06/3.49  sim_smt_subsumption:                    0
% 23.06/3.49  
%------------------------------------------------------------------------------
