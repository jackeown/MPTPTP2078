%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:34 EST 2020

% Result     : CounterSatisfiable 1.05s
% Output     : Saturation 1.05s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 587 expanded)
%              Number of clauses        :   32 ( 174 expanded)
%              Number of leaves         :    8 ( 161 expanded)
%              Depth                    :   18
%              Number of atoms          :  127 (2018 expanded)
%              Number of equality atoms :   82 (1156 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( r1_yellow_0(X0,X2)
               => k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2] :
                  ( r1_yellow_0(X0,X2)
                 => k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2] : k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] : k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] : k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ? [X2] : k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
     => k1_yellow_0(X0,sK2) != k1_yellow_0(X1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] : k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
     => ( ? [X2] : k1_yellow_0(sK1,X2) != k1_yellow_0(X0,X2)
        & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        & l1_orders_2(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] : k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] : k1_yellow_0(sK0,X2) != k1_yellow_0(X1,X2)
          & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( k1_yellow_0(sK0,sK2) != k1_yellow_0(sK1,sK2)
    & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    & l1_orders_2(sK1)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12,f11,f10])).

fof(f19,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f18,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f17,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f20,plain,(
    k1_yellow_0(sK0,sK2) != k1_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_55,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_231,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_4,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_321,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_517,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK1) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_321])).

cnf(c_0,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_5,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_63,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_5])).

cnf(c_64,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(unflattening,[status(thm)],[c_63])).

cnf(c_518,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK1) = X0
    | m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_321])).

cnf(c_535,plain,
    ( ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK1) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_518])).

cnf(c_539,plain,
    ( u1_struct_0(sK1) = X0
    | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_517,c_64,c_535])).

cnf(c_540,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK1) = X0 ),
    inference(renaming,[status(thm)],[c_539])).

cnf(c_545,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK0) ),
    inference(equality_resolution,[status(thm)],[c_540])).

cnf(c_623,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) ),
    inference(demodulation,[status(thm)],[c_545,c_4])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X0
    | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_322,plain,
    ( X0 = X1
    | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_722,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK1) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_623,c_322])).

cnf(c_320,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_64])).

cnf(c_622,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_545,c_320])).

cnf(c_723,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK1) = X1
    | m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_623,c_322])).

cnf(c_743,plain,
    ( u1_orders_2(sK1) = X1
    | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_722,c_622,c_723])).

cnf(c_744,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK1) = X1 ),
    inference(renaming,[status(thm)],[c_743])).

cnf(c_749,plain,
    ( u1_orders_2(sK1) = u1_orders_2(sK0) ),
    inference(equality_resolution,[status(thm)],[c_744])).

cnf(c_751,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK0) = X1 ),
    inference(demodulation,[status(thm)],[c_749,c_744])).

cnf(c_547,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK0) = X0 ),
    inference(demodulation,[status(thm)],[c_545,c_540])).

cnf(c_6,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_70,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_6])).

cnf(c_71,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_70])).

cnf(c_319,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_71])).

cnf(c_3,negated_conjecture,
    ( k1_yellow_0(sK0,sK2) != k1_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:57:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.05/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.05/0.99  
% 1.05/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.05/0.99  
% 1.05/0.99  ------  iProver source info
% 1.05/0.99  
% 1.05/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.05/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.05/0.99  git: non_committed_changes: false
% 1.05/0.99  git: last_make_outside_of_git: false
% 1.05/0.99  
% 1.05/0.99  ------ 
% 1.05/0.99  
% 1.05/0.99  ------ Input Options
% 1.05/0.99  
% 1.05/0.99  --out_options                           all
% 1.05/0.99  --tptp_safe_out                         true
% 1.05/0.99  --problem_path                          ""
% 1.05/0.99  --include_path                          ""
% 1.05/0.99  --clausifier                            res/vclausify_rel
% 1.05/0.99  --clausifier_options                    --mode clausify
% 1.05/0.99  --stdin                                 false
% 1.05/0.99  --stats_out                             all
% 1.05/0.99  
% 1.05/0.99  ------ General Options
% 1.05/0.99  
% 1.05/0.99  --fof                                   false
% 1.05/0.99  --time_out_real                         305.
% 1.05/0.99  --time_out_virtual                      -1.
% 1.05/0.99  --symbol_type_check                     false
% 1.05/0.99  --clausify_out                          false
% 1.05/0.99  --sig_cnt_out                           false
% 1.05/0.99  --trig_cnt_out                          false
% 1.05/0.99  --trig_cnt_out_tolerance                1.
% 1.05/0.99  --trig_cnt_out_sk_spl                   false
% 1.05/0.99  --abstr_cl_out                          false
% 1.05/0.99  
% 1.05/0.99  ------ Global Options
% 1.05/0.99  
% 1.05/0.99  --schedule                              default
% 1.05/0.99  --add_important_lit                     false
% 1.05/0.99  --prop_solver_per_cl                    1000
% 1.05/0.99  --min_unsat_core                        false
% 1.05/0.99  --soft_assumptions                      false
% 1.05/0.99  --soft_lemma_size                       3
% 1.05/0.99  --prop_impl_unit_size                   0
% 1.05/0.99  --prop_impl_unit                        []
% 1.05/0.99  --share_sel_clauses                     true
% 1.05/0.99  --reset_solvers                         false
% 1.05/0.99  --bc_imp_inh                            [conj_cone]
% 1.05/0.99  --conj_cone_tolerance                   3.
% 1.05/0.99  --extra_neg_conj                        none
% 1.05/0.99  --large_theory_mode                     true
% 1.05/0.99  --prolific_symb_bound                   200
% 1.05/0.99  --lt_threshold                          2000
% 1.05/0.99  --clause_weak_htbl                      true
% 1.05/0.99  --gc_record_bc_elim                     false
% 1.05/0.99  
% 1.05/0.99  ------ Preprocessing Options
% 1.05/0.99  
% 1.05/0.99  --preprocessing_flag                    true
% 1.05/0.99  --time_out_prep_mult                    0.1
% 1.05/0.99  --splitting_mode                        input
% 1.05/0.99  --splitting_grd                         true
% 1.05/0.99  --splitting_cvd                         false
% 1.05/0.99  --splitting_cvd_svl                     false
% 1.05/0.99  --splitting_nvd                         32
% 1.05/0.99  --sub_typing                            true
% 1.05/0.99  --prep_gs_sim                           true
% 1.05/0.99  --prep_unflatten                        true
% 1.05/0.99  --prep_res_sim                          true
% 1.05/0.99  --prep_upred                            true
% 1.05/0.99  --prep_sem_filter                       exhaustive
% 1.05/0.99  --prep_sem_filter_out                   false
% 1.05/0.99  --pred_elim                             true
% 1.05/0.99  --res_sim_input                         true
% 1.05/0.99  --eq_ax_congr_red                       true
% 1.05/0.99  --pure_diseq_elim                       true
% 1.05/0.99  --brand_transform                       false
% 1.05/0.99  --non_eq_to_eq                          false
% 1.05/0.99  --prep_def_merge                        true
% 1.05/0.99  --prep_def_merge_prop_impl              false
% 1.05/0.99  --prep_def_merge_mbd                    true
% 1.05/0.99  --prep_def_merge_tr_red                 false
% 1.05/0.99  --prep_def_merge_tr_cl                  false
% 1.05/0.99  --smt_preprocessing                     true
% 1.05/0.99  --smt_ac_axioms                         fast
% 1.05/0.99  --preprocessed_out                      false
% 1.05/0.99  --preprocessed_stats                    false
% 1.05/0.99  
% 1.05/0.99  ------ Abstraction refinement Options
% 1.05/0.99  
% 1.05/0.99  --abstr_ref                             []
% 1.05/0.99  --abstr_ref_prep                        false
% 1.05/0.99  --abstr_ref_until_sat                   false
% 1.05/0.99  --abstr_ref_sig_restrict                funpre
% 1.05/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.05/0.99  --abstr_ref_under                       []
% 1.05/0.99  
% 1.05/0.99  ------ SAT Options
% 1.05/0.99  
% 1.05/0.99  --sat_mode                              false
% 1.05/0.99  --sat_fm_restart_options                ""
% 1.05/0.99  --sat_gr_def                            false
% 1.05/0.99  --sat_epr_types                         true
% 1.05/0.99  --sat_non_cyclic_types                  false
% 1.05/0.99  --sat_finite_models                     false
% 1.05/0.99  --sat_fm_lemmas                         false
% 1.05/0.99  --sat_fm_prep                           false
% 1.05/0.99  --sat_fm_uc_incr                        true
% 1.05/0.99  --sat_out_model                         small
% 1.05/0.99  --sat_out_clauses                       false
% 1.05/0.99  
% 1.05/0.99  ------ QBF Options
% 1.05/0.99  
% 1.05/0.99  --qbf_mode                              false
% 1.05/0.99  --qbf_elim_univ                         false
% 1.05/0.99  --qbf_dom_inst                          none
% 1.05/0.99  --qbf_dom_pre_inst                      false
% 1.05/0.99  --qbf_sk_in                             false
% 1.05/0.99  --qbf_pred_elim                         true
% 1.05/0.99  --qbf_split                             512
% 1.05/0.99  
% 1.05/0.99  ------ BMC1 Options
% 1.05/0.99  
% 1.05/0.99  --bmc1_incremental                      false
% 1.05/0.99  --bmc1_axioms                           reachable_all
% 1.05/0.99  --bmc1_min_bound                        0
% 1.05/0.99  --bmc1_max_bound                        -1
% 1.05/0.99  --bmc1_max_bound_default                -1
% 1.05/0.99  --bmc1_symbol_reachability              true
% 1.05/0.99  --bmc1_property_lemmas                  false
% 1.05/0.99  --bmc1_k_induction                      false
% 1.05/0.99  --bmc1_non_equiv_states                 false
% 1.05/0.99  --bmc1_deadlock                         false
% 1.05/0.99  --bmc1_ucm                              false
% 1.05/0.99  --bmc1_add_unsat_core                   none
% 1.05/0.99  --bmc1_unsat_core_children              false
% 1.05/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.05/0.99  --bmc1_out_stat                         full
% 1.05/0.99  --bmc1_ground_init                      false
% 1.05/0.99  --bmc1_pre_inst_next_state              false
% 1.05/0.99  --bmc1_pre_inst_state                   false
% 1.05/0.99  --bmc1_pre_inst_reach_state             false
% 1.05/0.99  --bmc1_out_unsat_core                   false
% 1.05/0.99  --bmc1_aig_witness_out                  false
% 1.05/0.99  --bmc1_verbose                          false
% 1.05/0.99  --bmc1_dump_clauses_tptp                false
% 1.05/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.05/0.99  --bmc1_dump_file                        -
% 1.05/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.05/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.05/0.99  --bmc1_ucm_extend_mode                  1
% 1.05/0.99  --bmc1_ucm_init_mode                    2
% 1.05/0.99  --bmc1_ucm_cone_mode                    none
% 1.05/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.05/0.99  --bmc1_ucm_relax_model                  4
% 1.05/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.05/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.05/0.99  --bmc1_ucm_layered_model                none
% 1.05/0.99  --bmc1_ucm_max_lemma_size               10
% 1.05/0.99  
% 1.05/0.99  ------ AIG Options
% 1.05/0.99  
% 1.05/0.99  --aig_mode                              false
% 1.05/0.99  
% 1.05/0.99  ------ Instantiation Options
% 1.05/0.99  
% 1.05/0.99  --instantiation_flag                    true
% 1.05/0.99  --inst_sos_flag                         false
% 1.05/0.99  --inst_sos_phase                        true
% 1.05/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.05/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.05/0.99  --inst_lit_sel_side                     num_symb
% 1.05/0.99  --inst_solver_per_active                1400
% 1.05/0.99  --inst_solver_calls_frac                1.
% 1.05/0.99  --inst_passive_queue_type               priority_queues
% 1.05/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.05/0.99  --inst_passive_queues_freq              [25;2]
% 1.05/0.99  --inst_dismatching                      true
% 1.05/0.99  --inst_eager_unprocessed_to_passive     true
% 1.05/0.99  --inst_prop_sim_given                   true
% 1.05/0.99  --inst_prop_sim_new                     false
% 1.05/0.99  --inst_subs_new                         false
% 1.05/0.99  --inst_eq_res_simp                      false
% 1.05/0.99  --inst_subs_given                       false
% 1.05/0.99  --inst_orphan_elimination               true
% 1.05/0.99  --inst_learning_loop_flag               true
% 1.05/0.99  --inst_learning_start                   3000
% 1.05/0.99  --inst_learning_factor                  2
% 1.05/0.99  --inst_start_prop_sim_after_learn       3
% 1.05/0.99  --inst_sel_renew                        solver
% 1.05/0.99  --inst_lit_activity_flag                true
% 1.05/0.99  --inst_restr_to_given                   false
% 1.05/0.99  --inst_activity_threshold               500
% 1.05/0.99  --inst_out_proof                        true
% 1.05/0.99  
% 1.05/0.99  ------ Resolution Options
% 1.05/0.99  
% 1.05/0.99  --resolution_flag                       true
% 1.05/0.99  --res_lit_sel                           adaptive
% 1.05/0.99  --res_lit_sel_side                      none
% 1.05/0.99  --res_ordering                          kbo
% 1.05/0.99  --res_to_prop_solver                    active
% 1.05/0.99  --res_prop_simpl_new                    false
% 1.05/0.99  --res_prop_simpl_given                  true
% 1.05/0.99  --res_passive_queue_type                priority_queues
% 1.05/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.05/0.99  --res_passive_queues_freq               [15;5]
% 1.05/0.99  --res_forward_subs                      full
% 1.05/0.99  --res_backward_subs                     full
% 1.05/0.99  --res_forward_subs_resolution           true
% 1.05/0.99  --res_backward_subs_resolution          true
% 1.05/0.99  --res_orphan_elimination                true
% 1.05/0.99  --res_time_limit                        2.
% 1.05/0.99  --res_out_proof                         true
% 1.05/0.99  
% 1.05/0.99  ------ Superposition Options
% 1.05/0.99  
% 1.05/0.99  --superposition_flag                    true
% 1.05/0.99  --sup_passive_queue_type                priority_queues
% 1.05/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.05/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.05/0.99  --demod_completeness_check              fast
% 1.05/0.99  --demod_use_ground                      true
% 1.05/0.99  --sup_to_prop_solver                    passive
% 1.05/0.99  --sup_prop_simpl_new                    true
% 1.05/0.99  --sup_prop_simpl_given                  true
% 1.05/0.99  --sup_fun_splitting                     false
% 1.05/0.99  --sup_smt_interval                      50000
% 1.05/0.99  
% 1.05/0.99  ------ Superposition Simplification Setup
% 1.05/0.99  
% 1.05/0.99  --sup_indices_passive                   []
% 1.05/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.05/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.05/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.05/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.05/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.05/0.99  --sup_full_bw                           [BwDemod]
% 1.05/0.99  --sup_immed_triv                        [TrivRules]
% 1.05/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.05/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.05/0.99  --sup_immed_bw_main                     []
% 1.05/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.05/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.05/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.05/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.05/0.99  
% 1.05/0.99  ------ Combination Options
% 1.05/0.99  
% 1.05/0.99  --comb_res_mult                         3
% 1.05/0.99  --comb_sup_mult                         2
% 1.05/0.99  --comb_inst_mult                        10
% 1.05/0.99  
% 1.05/0.99  ------ Debug Options
% 1.05/0.99  
% 1.05/0.99  --dbg_backtrace                         false
% 1.05/0.99  --dbg_dump_prop_clauses                 false
% 1.05/0.99  --dbg_dump_prop_clauses_file            -
% 1.05/0.99  --dbg_out_stat                          false
% 1.05/0.99  ------ Parsing...
% 1.05/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.05/0.99  
% 1.05/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.05/0.99  
% 1.05/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.05/0.99  
% 1.05/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.05/0.99  ------ Proving...
% 1.05/0.99  ------ Problem Properties 
% 1.05/0.99  
% 1.05/0.99  
% 1.05/0.99  clauses                                 6
% 1.05/0.99  conjectures                             2
% 1.05/0.99  EPR                                     0
% 1.05/0.99  Horn                                    6
% 1.05/0.99  unary                                   4
% 1.05/0.99  binary                                  0
% 1.05/0.99  lits                                    10
% 1.05/0.99  lits eq                                 6
% 1.05/0.99  fd_pure                                 0
% 1.05/0.99  fd_pseudo                               0
% 1.05/0.99  fd_cond                                 0
% 1.05/0.99  fd_pseudo_cond                          2
% 1.05/0.99  AC symbols                              0
% 1.05/0.99  
% 1.05/0.99  ------ Schedule dynamic 5 is on 
% 1.05/0.99  
% 1.05/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.05/0.99  
% 1.05/0.99  
% 1.05/0.99  ------ 
% 1.05/0.99  Current options:
% 1.05/0.99  ------ 
% 1.05/0.99  
% 1.05/0.99  ------ Input Options
% 1.05/0.99  
% 1.05/0.99  --out_options                           all
% 1.05/0.99  --tptp_safe_out                         true
% 1.05/0.99  --problem_path                          ""
% 1.05/0.99  --include_path                          ""
% 1.05/0.99  --clausifier                            res/vclausify_rel
% 1.05/0.99  --clausifier_options                    --mode clausify
% 1.05/0.99  --stdin                                 false
% 1.05/0.99  --stats_out                             all
% 1.05/0.99  
% 1.05/0.99  ------ General Options
% 1.05/0.99  
% 1.05/0.99  --fof                                   false
% 1.05/0.99  --time_out_real                         305.
% 1.05/0.99  --time_out_virtual                      -1.
% 1.05/0.99  --symbol_type_check                     false
% 1.05/0.99  --clausify_out                          false
% 1.05/0.99  --sig_cnt_out                           false
% 1.05/0.99  --trig_cnt_out                          false
% 1.05/0.99  --trig_cnt_out_tolerance                1.
% 1.05/0.99  --trig_cnt_out_sk_spl                   false
% 1.05/0.99  --abstr_cl_out                          false
% 1.05/0.99  
% 1.05/0.99  ------ Global Options
% 1.05/0.99  
% 1.05/0.99  --schedule                              default
% 1.05/0.99  --add_important_lit                     false
% 1.05/0.99  --prop_solver_per_cl                    1000
% 1.05/0.99  --min_unsat_core                        false
% 1.05/0.99  --soft_assumptions                      false
% 1.05/0.99  --soft_lemma_size                       3
% 1.05/0.99  --prop_impl_unit_size                   0
% 1.05/0.99  --prop_impl_unit                        []
% 1.05/0.99  --share_sel_clauses                     true
% 1.05/0.99  --reset_solvers                         false
% 1.05/0.99  --bc_imp_inh                            [conj_cone]
% 1.05/0.99  --conj_cone_tolerance                   3.
% 1.05/0.99  --extra_neg_conj                        none
% 1.05/0.99  --large_theory_mode                     true
% 1.05/0.99  --prolific_symb_bound                   200
% 1.05/0.99  --lt_threshold                          2000
% 1.05/0.99  --clause_weak_htbl                      true
% 1.05/0.99  --gc_record_bc_elim                     false
% 1.05/0.99  
% 1.05/0.99  ------ Preprocessing Options
% 1.05/0.99  
% 1.05/0.99  --preprocessing_flag                    true
% 1.05/0.99  --time_out_prep_mult                    0.1
% 1.05/0.99  --splitting_mode                        input
% 1.05/0.99  --splitting_grd                         true
% 1.05/0.99  --splitting_cvd                         false
% 1.05/0.99  --splitting_cvd_svl                     false
% 1.05/0.99  --splitting_nvd                         32
% 1.05/0.99  --sub_typing                            true
% 1.05/0.99  --prep_gs_sim                           true
% 1.05/0.99  --prep_unflatten                        true
% 1.05/0.99  --prep_res_sim                          true
% 1.05/0.99  --prep_upred                            true
% 1.05/0.99  --prep_sem_filter                       exhaustive
% 1.05/0.99  --prep_sem_filter_out                   false
% 1.05/0.99  --pred_elim                             true
% 1.05/0.99  --res_sim_input                         true
% 1.05/0.99  --eq_ax_congr_red                       true
% 1.05/0.99  --pure_diseq_elim                       true
% 1.05/0.99  --brand_transform                       false
% 1.05/0.99  --non_eq_to_eq                          false
% 1.05/0.99  --prep_def_merge                        true
% 1.05/0.99  --prep_def_merge_prop_impl              false
% 1.05/0.99  --prep_def_merge_mbd                    true
% 1.05/0.99  --prep_def_merge_tr_red                 false
% 1.05/0.99  --prep_def_merge_tr_cl                  false
% 1.05/0.99  --smt_preprocessing                     true
% 1.05/0.99  --smt_ac_axioms                         fast
% 1.05/0.99  --preprocessed_out                      false
% 1.05/0.99  --preprocessed_stats                    false
% 1.05/0.99  
% 1.05/0.99  ------ Abstraction refinement Options
% 1.05/0.99  
% 1.05/0.99  --abstr_ref                             []
% 1.05/0.99  --abstr_ref_prep                        false
% 1.05/0.99  --abstr_ref_until_sat                   false
% 1.05/0.99  --abstr_ref_sig_restrict                funpre
% 1.05/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.05/0.99  --abstr_ref_under                       []
% 1.05/0.99  
% 1.05/0.99  ------ SAT Options
% 1.05/0.99  
% 1.05/0.99  --sat_mode                              false
% 1.05/0.99  --sat_fm_restart_options                ""
% 1.05/0.99  --sat_gr_def                            false
% 1.05/0.99  --sat_epr_types                         true
% 1.05/0.99  --sat_non_cyclic_types                  false
% 1.05/0.99  --sat_finite_models                     false
% 1.05/0.99  --sat_fm_lemmas                         false
% 1.05/0.99  --sat_fm_prep                           false
% 1.05/0.99  --sat_fm_uc_incr                        true
% 1.05/0.99  --sat_out_model                         small
% 1.05/0.99  --sat_out_clauses                       false
% 1.05/0.99  
% 1.05/0.99  ------ QBF Options
% 1.05/0.99  
% 1.05/0.99  --qbf_mode                              false
% 1.05/0.99  --qbf_elim_univ                         false
% 1.05/0.99  --qbf_dom_inst                          none
% 1.05/0.99  --qbf_dom_pre_inst                      false
% 1.05/0.99  --qbf_sk_in                             false
% 1.05/0.99  --qbf_pred_elim                         true
% 1.05/0.99  --qbf_split                             512
% 1.05/0.99  
% 1.05/0.99  ------ BMC1 Options
% 1.05/0.99  
% 1.05/0.99  --bmc1_incremental                      false
% 1.05/0.99  --bmc1_axioms                           reachable_all
% 1.05/0.99  --bmc1_min_bound                        0
% 1.05/0.99  --bmc1_max_bound                        -1
% 1.05/0.99  --bmc1_max_bound_default                -1
% 1.05/0.99  --bmc1_symbol_reachability              true
% 1.05/0.99  --bmc1_property_lemmas                  false
% 1.05/0.99  --bmc1_k_induction                      false
% 1.05/0.99  --bmc1_non_equiv_states                 false
% 1.05/0.99  --bmc1_deadlock                         false
% 1.05/0.99  --bmc1_ucm                              false
% 1.05/0.99  --bmc1_add_unsat_core                   none
% 1.05/0.99  --bmc1_unsat_core_children              false
% 1.05/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.05/0.99  --bmc1_out_stat                         full
% 1.05/0.99  --bmc1_ground_init                      false
% 1.05/0.99  --bmc1_pre_inst_next_state              false
% 1.05/0.99  --bmc1_pre_inst_state                   false
% 1.05/0.99  --bmc1_pre_inst_reach_state             false
% 1.05/0.99  --bmc1_out_unsat_core                   false
% 1.05/0.99  --bmc1_aig_witness_out                  false
% 1.05/0.99  --bmc1_verbose                          false
% 1.05/0.99  --bmc1_dump_clauses_tptp                false
% 1.05/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.05/0.99  --bmc1_dump_file                        -
% 1.05/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.05/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.05/0.99  --bmc1_ucm_extend_mode                  1
% 1.05/0.99  --bmc1_ucm_init_mode                    2
% 1.05/0.99  --bmc1_ucm_cone_mode                    none
% 1.05/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.05/0.99  --bmc1_ucm_relax_model                  4
% 1.05/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.05/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.05/0.99  --bmc1_ucm_layered_model                none
% 1.05/0.99  --bmc1_ucm_max_lemma_size               10
% 1.05/0.99  
% 1.05/0.99  ------ AIG Options
% 1.05/0.99  
% 1.05/0.99  --aig_mode                              false
% 1.05/0.99  
% 1.05/0.99  ------ Instantiation Options
% 1.05/0.99  
% 1.05/0.99  --instantiation_flag                    true
% 1.05/0.99  --inst_sos_flag                         false
% 1.05/0.99  --inst_sos_phase                        true
% 1.05/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.05/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.05/0.99  --inst_lit_sel_side                     none
% 1.05/0.99  --inst_solver_per_active                1400
% 1.05/0.99  --inst_solver_calls_frac                1.
% 1.05/0.99  --inst_passive_queue_type               priority_queues
% 1.05/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.05/0.99  --inst_passive_queues_freq              [25;2]
% 1.05/0.99  --inst_dismatching                      true
% 1.05/0.99  --inst_eager_unprocessed_to_passive     true
% 1.05/0.99  --inst_prop_sim_given                   true
% 1.05/0.99  --inst_prop_sim_new                     false
% 1.05/0.99  --inst_subs_new                         false
% 1.05/0.99  --inst_eq_res_simp                      false
% 1.05/0.99  --inst_subs_given                       false
% 1.05/0.99  --inst_orphan_elimination               true
% 1.05/0.99  --inst_learning_loop_flag               true
% 1.05/0.99  --inst_learning_start                   3000
% 1.05/0.99  --inst_learning_factor                  2
% 1.05/0.99  --inst_start_prop_sim_after_learn       3
% 1.05/0.99  --inst_sel_renew                        solver
% 1.05/0.99  --inst_lit_activity_flag                true
% 1.05/0.99  --inst_restr_to_given                   false
% 1.05/0.99  --inst_activity_threshold               500
% 1.05/0.99  --inst_out_proof                        true
% 1.05/0.99  
% 1.05/0.99  ------ Resolution Options
% 1.05/0.99  
% 1.05/0.99  --resolution_flag                       false
% 1.05/0.99  --res_lit_sel                           adaptive
% 1.05/0.99  --res_lit_sel_side                      none
% 1.05/0.99  --res_ordering                          kbo
% 1.05/0.99  --res_to_prop_solver                    active
% 1.05/0.99  --res_prop_simpl_new                    false
% 1.05/0.99  --res_prop_simpl_given                  true
% 1.05/0.99  --res_passive_queue_type                priority_queues
% 1.05/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.05/0.99  --res_passive_queues_freq               [15;5]
% 1.05/0.99  --res_forward_subs                      full
% 1.05/0.99  --res_backward_subs                     full
% 1.05/0.99  --res_forward_subs_resolution           true
% 1.05/0.99  --res_backward_subs_resolution          true
% 1.05/0.99  --res_orphan_elimination                true
% 1.05/0.99  --res_time_limit                        2.
% 1.05/0.99  --res_out_proof                         true
% 1.05/0.99  
% 1.05/0.99  ------ Superposition Options
% 1.05/0.99  
% 1.05/0.99  --superposition_flag                    true
% 1.05/0.99  --sup_passive_queue_type                priority_queues
% 1.05/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.05/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.05/0.99  --demod_completeness_check              fast
% 1.05/0.99  --demod_use_ground                      true
% 1.05/0.99  --sup_to_prop_solver                    passive
% 1.05/0.99  --sup_prop_simpl_new                    true
% 1.05/0.99  --sup_prop_simpl_given                  true
% 1.05/0.99  --sup_fun_splitting                     false
% 1.05/0.99  --sup_smt_interval                      50000
% 1.05/0.99  
% 1.05/0.99  ------ Superposition Simplification Setup
% 1.05/0.99  
% 1.05/0.99  --sup_indices_passive                   []
% 1.05/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.05/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.05/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.05/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.05/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.05/0.99  --sup_full_bw                           [BwDemod]
% 1.05/0.99  --sup_immed_triv                        [TrivRules]
% 1.05/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.05/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.05/0.99  --sup_immed_bw_main                     []
% 1.05/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.05/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.05/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.05/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.05/0.99  
% 1.05/0.99  ------ Combination Options
% 1.05/0.99  
% 1.05/0.99  --comb_res_mult                         3
% 1.05/0.99  --comb_sup_mult                         2
% 1.05/0.99  --comb_inst_mult                        10
% 1.05/0.99  
% 1.05/0.99  ------ Debug Options
% 1.05/0.99  
% 1.05/0.99  --dbg_backtrace                         false
% 1.05/0.99  --dbg_dump_prop_clauses                 false
% 1.05/0.99  --dbg_dump_prop_clauses_file            -
% 1.05/0.99  --dbg_out_stat                          false
% 1.05/0.99  
% 1.05/0.99  
% 1.05/0.99  
% 1.05/0.99  
% 1.05/0.99  ------ Proving...
% 1.05/0.99  
% 1.05/0.99  
% 1.05/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 1.05/0.99  
% 1.05/0.99  % SZS output start Saturation for theBenchmark.p
% 1.05/0.99  
% 1.05/0.99  fof(f3,conjecture,(
% 1.05/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) => ! [X2] : (r1_yellow_0(X0,X2) => k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)))))),
% 1.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.05/0.99  
% 1.05/0.99  fof(f4,negated_conjecture,(
% 1.05/0.99    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) => ! [X2] : (r1_yellow_0(X0,X2) => k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)))))),
% 1.05/0.99    inference(negated_conjecture,[],[f3])).
% 1.05/0.99  
% 1.05/0.99  fof(f5,plain,(
% 1.05/0.99    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) => ! [X2] : k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2))))),
% 1.05/0.99    inference(pure_predicate_removal,[],[f4])).
% 1.05/0.99  
% 1.05/0.99  fof(f8,plain,(
% 1.05/0.99    ? [X0] : (? [X1] : ((? [X2] : k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) & l1_orders_2(X1)) & l1_orders_2(X0))),
% 1.05/0.99    inference(ennf_transformation,[],[f5])).
% 1.05/0.99  
% 1.05/0.99  fof(f9,plain,(
% 1.05/0.99    ? [X0] : (? [X1] : (? [X2] : k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) & l1_orders_2(X1)) & l1_orders_2(X0))),
% 1.05/0.99    inference(flattening,[],[f8])).
% 1.05/0.99  
% 1.05/0.99  fof(f12,plain,(
% 1.05/0.99    ( ! [X0,X1] : (? [X2] : k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2) => k1_yellow_0(X0,sK2) != k1_yellow_0(X1,sK2)) )),
% 1.05/0.99    introduced(choice_axiom,[])).
% 1.05/0.99  
% 1.05/0.99  fof(f11,plain,(
% 1.05/0.99    ( ! [X0] : (? [X1] : (? [X2] : k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) & l1_orders_2(X1)) => (? [X2] : k1_yellow_0(sK1,X2) != k1_yellow_0(X0,X2) & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) & l1_orders_2(sK1))) )),
% 1.05/0.99    introduced(choice_axiom,[])).
% 1.05/0.99  
% 1.05/0.99  fof(f10,plain,(
% 1.05/0.99    ? [X0] : (? [X1] : (? [X2] : k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) & l1_orders_2(X1)) & l1_orders_2(X0)) => (? [X1] : (? [X2] : k1_yellow_0(sK0,X2) != k1_yellow_0(X1,X2) & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) & l1_orders_2(X1)) & l1_orders_2(sK0))),
% 1.05/0.99    introduced(choice_axiom,[])).
% 1.05/0.99  
% 1.05/0.99  fof(f13,plain,(
% 1.05/0.99    (k1_yellow_0(sK0,sK2) != k1_yellow_0(sK1,sK2) & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) & l1_orders_2(sK1)) & l1_orders_2(sK0)),
% 1.05/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12,f11,f10])).
% 1.05/0.99  
% 1.05/0.99  fof(f19,plain,(
% 1.05/0.99    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))),
% 1.05/0.99    inference(cnf_transformation,[],[f13])).
% 1.05/0.99  
% 1.05/0.99  fof(f2,axiom,(
% 1.05/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2,X3] : (g1_orders_2(X0,X1) = g1_orders_2(X2,X3) => (X1 = X3 & X0 = X2)))),
% 1.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.05/0.99  
% 1.05/0.99  fof(f7,plain,(
% 1.05/0.99    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 1.05/0.99    inference(ennf_transformation,[],[f2])).
% 1.05/0.99  
% 1.05/0.99  fof(f15,plain,(
% 1.05/0.99    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.05/0.99    inference(cnf_transformation,[],[f7])).
% 1.05/0.99  
% 1.05/0.99  fof(f1,axiom,(
% 1.05/0.99    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 1.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.05/0.99  
% 1.05/0.99  fof(f6,plain,(
% 1.05/0.99    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.05/0.99    inference(ennf_transformation,[],[f1])).
% 1.05/0.99  
% 1.05/0.99  fof(f14,plain,(
% 1.05/0.99    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 1.05/0.99    inference(cnf_transformation,[],[f6])).
% 1.05/0.99  
% 1.05/0.99  fof(f18,plain,(
% 1.05/0.99    l1_orders_2(sK1)),
% 1.05/0.99    inference(cnf_transformation,[],[f13])).
% 1.05/0.99  
% 1.05/0.99  fof(f16,plain,(
% 1.05/0.99    ( ! [X2,X0,X3,X1] : (X1 = X3 | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.05/0.99    inference(cnf_transformation,[],[f7])).
% 1.05/0.99  
% 1.05/0.99  fof(f17,plain,(
% 1.05/0.99    l1_orders_2(sK0)),
% 1.05/0.99    inference(cnf_transformation,[],[f13])).
% 1.05/0.99  
% 1.05/0.99  fof(f20,plain,(
% 1.05/0.99    k1_yellow_0(sK0,sK2) != k1_yellow_0(sK1,sK2)),
% 1.05/0.99    inference(cnf_transformation,[],[f13])).
% 1.05/0.99  
% 1.05/0.99  cnf(c_55,plain,
% 1.05/0.99      ( ~ l1_orders_2(X0) | l1_orders_2(X1) | X1 != X0 ),
% 1.05/0.99      theory(equality) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_231,plain,( X0_2 = X0_2 ),theory(equality) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_4,negated_conjecture,
% 1.05/0.99      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
% 1.05/0.99      inference(cnf_transformation,[],[f19]) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_2,plain,
% 1.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.05/0.99      | X2 = X1
% 1.05/0.99      | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
% 1.05/0.99      inference(cnf_transformation,[],[f15]) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_321,plain,
% 1.05/0.99      ( X0 = X1
% 1.05/0.99      | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
% 1.05/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
% 1.05/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_517,plain,
% 1.05/0.99      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
% 1.05/0.99      | u1_struct_0(sK1) = X0
% 1.05/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 1.05/0.99      inference(superposition,[status(thm)],[c_4,c_321]) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_0,plain,
% 1.05/0.99      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 1.05/0.99      | ~ l1_orders_2(X0) ),
% 1.05/0.99      inference(cnf_transformation,[],[f14]) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_5,negated_conjecture,
% 1.05/0.99      ( l1_orders_2(sK1) ),
% 1.05/0.99      inference(cnf_transformation,[],[f18]) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_63,plain,
% 1.05/0.99      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 1.05/0.99      | sK1 != X0 ),
% 1.05/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_5]) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_64,plain,
% 1.05/0.99      ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
% 1.05/0.99      inference(unflattening,[status(thm)],[c_63]) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_518,plain,
% 1.05/0.99      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
% 1.05/0.99      | u1_struct_0(sK1) = X0
% 1.05/0.99      | m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top ),
% 1.05/0.99      inference(superposition,[status(thm)],[c_4,c_321]) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_535,plain,
% 1.05/0.99      ( ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 1.05/0.99      | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
% 1.05/0.99      | u1_struct_0(sK1) = X0 ),
% 1.05/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_518]) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_539,plain,
% 1.05/0.99      ( u1_struct_0(sK1) = X0
% 1.05/0.99      | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1) ),
% 1.05/0.99      inference(global_propositional_subsumption,
% 1.05/0.99                [status(thm)],
% 1.05/0.99                [c_517,c_64,c_535]) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_540,plain,
% 1.05/0.99      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
% 1.05/0.99      | u1_struct_0(sK1) = X0 ),
% 1.05/0.99      inference(renaming,[status(thm)],[c_539]) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_545,plain,
% 1.05/0.99      ( u1_struct_0(sK1) = u1_struct_0(sK0) ),
% 1.05/0.99      inference(equality_resolution,[status(thm)],[c_540]) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_623,plain,
% 1.05/0.99      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) ),
% 1.05/0.99      inference(demodulation,[status(thm)],[c_545,c_4]) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_1,plain,
% 1.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.05/0.99      | X2 = X0
% 1.05/0.99      | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
% 1.05/0.99      inference(cnf_transformation,[],[f16]) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_322,plain,
% 1.05/0.99      ( X0 = X1
% 1.05/0.99      | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
% 1.05/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
% 1.05/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_722,plain,
% 1.05/0.99      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
% 1.05/0.99      | u1_orders_2(sK1) = X1
% 1.05/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 1.05/0.99      inference(superposition,[status(thm)],[c_623,c_322]) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_320,plain,
% 1.05/0.99      ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
% 1.05/0.99      inference(predicate_to_equality,[status(thm)],[c_64]) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_622,plain,
% 1.05/0.99      ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = iProver_top ),
% 1.05/0.99      inference(demodulation,[status(thm)],[c_545,c_320]) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_723,plain,
% 1.05/0.99      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
% 1.05/0.99      | u1_orders_2(sK1) = X1
% 1.05/0.99      | m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top ),
% 1.05/0.99      inference(superposition,[status(thm)],[c_623,c_322]) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_743,plain,
% 1.05/0.99      ( u1_orders_2(sK1) = X1
% 1.05/0.99      | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1) ),
% 1.05/0.99      inference(global_propositional_subsumption,
% 1.05/0.99                [status(thm)],
% 1.05/0.99                [c_722,c_622,c_723]) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_744,plain,
% 1.05/0.99      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
% 1.05/0.99      | u1_orders_2(sK1) = X1 ),
% 1.05/0.99      inference(renaming,[status(thm)],[c_743]) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_749,plain,
% 1.05/0.99      ( u1_orders_2(sK1) = u1_orders_2(sK0) ),
% 1.05/0.99      inference(equality_resolution,[status(thm)],[c_744]) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_751,plain,
% 1.05/0.99      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
% 1.05/0.99      | u1_orders_2(sK0) = X1 ),
% 1.05/0.99      inference(demodulation,[status(thm)],[c_749,c_744]) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_547,plain,
% 1.05/0.99      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X0,X1)
% 1.05/0.99      | u1_struct_0(sK0) = X0 ),
% 1.05/0.99      inference(demodulation,[status(thm)],[c_545,c_540]) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_6,negated_conjecture,
% 1.05/0.99      ( l1_orders_2(sK0) ),
% 1.05/0.99      inference(cnf_transformation,[],[f17]) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_70,plain,
% 1.05/0.99      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 1.05/0.99      | sK0 != X0 ),
% 1.05/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_6]) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_71,plain,
% 1.05/0.99      ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
% 1.05/0.99      inference(unflattening,[status(thm)],[c_70]) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_319,plain,
% 1.05/0.99      ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = iProver_top ),
% 1.05/0.99      inference(predicate_to_equality,[status(thm)],[c_71]) ).
% 1.05/0.99  
% 1.05/0.99  cnf(c_3,negated_conjecture,
% 1.05/0.99      ( k1_yellow_0(sK0,sK2) != k1_yellow_0(sK1,sK2) ),
% 1.05/0.99      inference(cnf_transformation,[],[f20]) ).
% 1.05/0.99  
% 1.05/0.99  
% 1.05/0.99  % SZS output end Saturation for theBenchmark.p
% 1.05/0.99  
% 1.05/0.99  ------                               Statistics
% 1.05/0.99  
% 1.05/0.99  ------ General
% 1.05/0.99  
% 1.05/0.99  abstr_ref_over_cycles:                  0
% 1.05/0.99  abstr_ref_under_cycles:                 0
% 1.05/0.99  gc_basic_clause_elim:                   0
% 1.05/0.99  forced_gc_time:                         0
% 1.05/0.99  parsing_time:                           0.009
% 1.05/0.99  unif_index_cands_time:                  0.
% 1.05/0.99  unif_index_add_time:                    0.
% 1.05/0.99  orderings_time:                         0.
% 1.05/0.99  out_proof_time:                         0.
% 1.05/0.99  total_time:                             0.066
% 1.05/0.99  num_of_symbols:                         42
% 1.05/0.99  num_of_terms:                           1312
% 1.05/0.99  
% 1.05/0.99  ------ Preprocessing
% 1.05/0.99  
% 1.05/0.99  num_of_splits:                          0
% 1.05/0.99  num_of_split_atoms:                     0
% 1.05/0.99  num_of_reused_defs:                     0
% 1.05/0.99  num_eq_ax_congr_red:                    0
% 1.05/0.99  num_of_sem_filtered_clauses:            1
% 1.05/0.99  num_of_subtypes:                        0
% 1.05/0.99  monotx_restored_types:                  0
% 1.05/0.99  sat_num_of_epr_types:                   0
% 1.05/0.99  sat_num_of_non_cyclic_types:            0
% 1.05/0.99  sat_guarded_non_collapsed_types:        0
% 1.05/0.99  num_pure_diseq_elim:                    0
% 1.05/0.99  simp_replaced_by:                       0
% 1.05/0.99  res_preprocessed:                       44
% 1.05/0.99  prep_upred:                             0
% 1.05/0.99  prep_unflattend:                        10
% 1.05/0.99  smt_new_axioms:                         0
% 1.05/0.99  pred_elim_cands:                        1
% 1.05/0.99  pred_elim:                              1
% 1.05/0.99  pred_elim_cl:                           1
% 1.05/0.99  pred_elim_cycles:                       3
% 1.05/0.99  merged_defs:                            0
% 1.05/0.99  merged_defs_ncl:                        0
% 1.05/0.99  bin_hyper_res:                          0
% 1.05/0.99  prep_cycles:                            4
% 1.05/0.99  pred_elim_time:                         0.002
% 1.05/0.99  splitting_time:                         0.
% 1.05/0.99  sem_filter_time:                        0.
% 1.05/0.99  monotx_time:                            0.
% 1.05/0.99  subtype_inf_time:                       0.
% 1.05/0.99  
% 1.05/0.99  ------ Problem properties
% 1.05/0.99  
% 1.05/0.99  clauses:                                6
% 1.05/0.99  conjectures:                            2
% 1.05/0.99  epr:                                    0
% 1.05/0.99  horn:                                   6
% 1.05/0.99  ground:                                 4
% 1.05/0.99  unary:                                  4
% 1.05/0.99  binary:                                 0
% 1.05/0.99  lits:                                   10
% 1.05/0.99  lits_eq:                                6
% 1.05/0.99  fd_pure:                                0
% 1.05/0.99  fd_pseudo:                              0
% 1.05/0.99  fd_cond:                                0
% 1.05/0.99  fd_pseudo_cond:                         2
% 1.05/0.99  ac_symbols:                             0
% 1.05/0.99  
% 1.05/0.99  ------ Propositional Solver
% 1.05/0.99  
% 1.05/0.99  prop_solver_calls:                      25
% 1.05/0.99  prop_fast_solver_calls:                 232
% 1.05/0.99  smt_solver_calls:                       0
% 1.05/0.99  smt_fast_solver_calls:                  0
% 1.05/0.99  prop_num_of_clauses:                    390
% 1.05/0.99  prop_preprocess_simplified:             1216
% 1.05/0.99  prop_fo_subsumed:                       2
% 1.05/0.99  prop_solver_time:                       0.
% 1.05/0.99  smt_solver_time:                        0.
% 1.05/0.99  smt_fast_solver_time:                   0.
% 1.05/0.99  prop_fast_solver_time:                  0.
% 1.05/0.99  prop_unsat_core_time:                   0.
% 1.05/0.99  
% 1.05/0.99  ------ QBF
% 1.05/0.99  
% 1.05/0.99  qbf_q_res:                              0
% 1.05/0.99  qbf_num_tautologies:                    0
% 1.05/0.99  qbf_prep_cycles:                        0
% 1.05/0.99  
% 1.05/0.99  ------ BMC1
% 1.05/0.99  
% 1.05/0.99  bmc1_current_bound:                     -1
% 1.05/0.99  bmc1_last_solved_bound:                 -1
% 1.05/0.99  bmc1_unsat_core_size:                   -1
% 1.05/0.99  bmc1_unsat_core_parents_size:           -1
% 1.05/0.99  bmc1_merge_next_fun:                    0
% 1.05/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.05/0.99  
% 1.05/0.99  ------ Instantiation
% 1.05/0.99  
% 1.05/0.99  inst_num_of_clauses:                    126
% 1.05/0.99  inst_num_in_passive:                    9
% 1.05/0.99  inst_num_in_active:                     65
% 1.05/0.99  inst_num_in_unprocessed:                52
% 1.05/0.99  inst_num_of_loops:                      70
% 1.05/0.99  inst_num_of_learning_restarts:          0
% 1.05/0.99  inst_num_moves_active_passive:          3
% 1.05/0.99  inst_lit_activity:                      0
% 1.05/0.99  inst_lit_activity_moves:                0
% 1.05/0.99  inst_num_tautologies:                   0
% 1.05/0.99  inst_num_prop_implied:                  0
% 1.05/0.99  inst_num_existing_simplified:           0
% 1.05/0.99  inst_num_eq_res_simplified:             0
% 1.05/0.99  inst_num_child_elim:                    0
% 1.05/0.99  inst_num_of_dismatching_blockings:      22
% 1.05/0.99  inst_num_of_non_proper_insts:           129
% 1.05/0.99  inst_num_of_duplicates:                 0
% 1.05/0.99  inst_inst_num_from_inst_to_res:         0
% 1.05/0.99  inst_dismatching_checking_time:         0.
% 1.05/0.99  
% 1.05/0.99  ------ Resolution
% 1.05/0.99  
% 1.05/0.99  res_num_of_clauses:                     0
% 1.05/0.99  res_num_in_passive:                     0
% 1.05/0.99  res_num_in_active:                      0
% 1.05/0.99  res_num_of_loops:                       48
% 1.05/0.99  res_forward_subset_subsumed:            18
% 1.05/0.99  res_backward_subset_subsumed:           0
% 1.05/0.99  res_forward_subsumed:                   0
% 1.05/0.99  res_backward_subsumed:                  0
% 1.05/0.99  res_forward_subsumption_resolution:     0
% 1.05/0.99  res_backward_subsumption_resolution:    0
% 1.05/0.99  res_clause_to_clause_subsumption:       35
% 1.05/0.99  res_orphan_elimination:                 0
% 1.05/0.99  res_tautology_del:                      7
% 1.05/0.99  res_num_eq_res_simplified:              0
% 1.05/0.99  res_num_sel_changes:                    0
% 1.05/0.99  res_moves_from_active_to_pass:          0
% 1.05/0.99  
% 1.05/0.99  ------ Superposition
% 1.05/0.99  
% 1.05/0.99  sup_time_total:                         0.
% 1.05/0.99  sup_time_generating:                    0.
% 1.05/0.99  sup_time_sim_full:                      0.
% 1.05/0.99  sup_time_sim_immed:                     0.
% 1.05/0.99  
% 1.05/0.99  sup_num_of_clauses:                     12
% 1.05/0.99  sup_num_in_active:                      8
% 1.05/0.99  sup_num_in_passive:                     4
% 1.05/0.99  sup_num_of_loops:                       13
% 1.05/0.99  sup_fw_superposition:                   5
% 1.05/0.99  sup_bw_superposition:                   4
% 1.05/0.99  sup_immediate_simplified:               2
% 1.05/0.99  sup_given_eliminated:                   2
% 1.05/0.99  comparisons_done:                       0
% 1.05/0.99  comparisons_avoided:                    0
% 1.05/0.99  
% 1.05/0.99  ------ Simplifications
% 1.05/0.99  
% 1.05/0.99  
% 1.05/0.99  sim_fw_subset_subsumed:                 2
% 1.05/0.99  sim_bw_subset_subsumed:                 2
% 1.05/0.99  sim_fw_subsumed:                        0
% 1.05/0.99  sim_bw_subsumed:                        0
% 1.05/0.99  sim_fw_subsumption_res:                 0
% 1.05/0.99  sim_bw_subsumption_res:                 0
% 1.05/0.99  sim_tautology_del:                      0
% 1.05/0.99  sim_eq_tautology_del:                   7
% 1.05/0.99  sim_eq_res_simp:                        0
% 1.05/0.99  sim_fw_demodulated:                     0
% 1.05/0.99  sim_bw_demodulated:                     5
% 1.05/0.99  sim_light_normalised:                   1
% 1.05/0.99  sim_joinable_taut:                      0
% 1.05/0.99  sim_joinable_simp:                      0
% 1.05/0.99  sim_ac_normalised:                      0
% 1.05/0.99  sim_smt_subsumption:                    0
% 1.05/0.99  
%------------------------------------------------------------------------------
