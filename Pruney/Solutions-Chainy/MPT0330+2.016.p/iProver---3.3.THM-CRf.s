%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:10 EST 2020

% Result     : Theorem 39.71s
% Output     : CNFRefutation 39.71s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 110 expanded)
%              Number of clauses        :   28 (  33 expanded)
%              Number of leaves         :    7 (  28 expanded)
%              Depth                    :   14
%              Number of atoms          :  102 ( 194 expanded)
%              Number of equality atoms :   39 (  77 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1))
      & k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_tarski(k2_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(X2,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f20,f18,f18])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f16,f18])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f15,f18,f18])).

fof(f19,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_tarski(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) = k2_zfmisc_1(k3_tarski(k2_tarski(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f19,f18,f18])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f17,f18,f18])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f11])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f12,f13])).

fof(f23,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f14])).

fof(f29,plain,(
    ~ r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) ),
    inference(definition_unfolding,[],[f23,f18,f18,f18])).

fof(f21,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f22,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_3,plain,
    ( k3_tarski(k2_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))) = k2_zfmisc_1(X0,k3_tarski(k2_tarski(X1,X2))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_67,plain,
    ( k3_tarski(k2_tarski(k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X0_38,X2_38))) = k2_zfmisc_1(X0_38,k3_tarski(k2_tarski(X1_38,X2_38))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_69,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | r1_tarski(X0_38,k3_tarski(k2_tarski(X2_38,X1_38))) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_174,plain,
    ( r1_tarski(X0_38,X1_38) != iProver_top
    | r1_tarski(X0_38,k3_tarski(k2_tarski(X2_38,X1_38))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_69])).

cnf(c_736,plain,
    ( r1_tarski(X0_38,k2_zfmisc_1(X1_38,X2_38)) != iProver_top
    | r1_tarski(X0_38,k2_zfmisc_1(X1_38,k3_tarski(k2_tarski(X3_38,X2_38)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_67,c_174])).

cnf(c_0,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_70,plain,
    ( k3_tarski(k2_tarski(X0_38,X1_38)) = k3_tarski(k2_tarski(X1_38,X0_38)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_467,plain,
    ( k3_tarski(k2_tarski(k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X0_38,X2_38))) = k2_zfmisc_1(X0_38,k3_tarski(k2_tarski(X2_38,X1_38))) ),
    inference(superposition,[status(thm)],[c_67,c_70])).

cnf(c_1471,plain,
    ( r1_tarski(X0_38,k2_zfmisc_1(X1_38,X2_38)) != iProver_top
    | r1_tarski(X0_38,k2_zfmisc_1(X1_38,k3_tarski(k2_tarski(X2_38,X3_38)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_467,c_174])).

cnf(c_4,plain,
    ( k3_tarski(k2_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(k3_tarski(k2_tarski(X0,X2)),X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_66,plain,
    ( k3_tarski(k2_tarski(k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X2_38,X1_38))) = k2_zfmisc_1(k3_tarski(k2_tarski(X0_38,X2_38)),X1_38) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X3))) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_68,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | ~ r1_tarski(X2_38,X3_38)
    | r1_tarski(k3_tarski(k2_tarski(X0_38,X2_38)),k3_tarski(k2_tarski(X1_38,X3_38))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_175,plain,
    ( r1_tarski(X0_38,X1_38) != iProver_top
    | r1_tarski(X2_38,X3_38) != iProver_top
    | r1_tarski(k3_tarski(k2_tarski(X0_38,X2_38)),k3_tarski(k2_tarski(X1_38,X3_38))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_68])).

cnf(c_937,plain,
    ( r1_tarski(X0_38,k2_zfmisc_1(X1_38,X2_38)) != iProver_top
    | r1_tarski(X3_38,k2_zfmisc_1(X4_38,X2_38)) != iProver_top
    | r1_tarski(k3_tarski(k2_tarski(X0_38,X3_38)),k2_zfmisc_1(k3_tarski(k2_tarski(X1_38,X4_38)),X2_38)) = iProver_top ),
    inference(superposition,[status(thm)],[c_66,c_175])).

cnf(c_5,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_65,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_176,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_65])).

cnf(c_111088,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_937,c_176])).

cnf(c_122816,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1471,c_111088])).

cnf(c_7,negated_conjecture,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_8,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_122841,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_122816,c_8])).

cnf(c_122847,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_736,c_122841])).

cnf(c_6,negated_conjecture,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_9,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_122847,c_9])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:01:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 39.71/5.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.71/5.49  
% 39.71/5.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.71/5.49  
% 39.71/5.49  ------  iProver source info
% 39.71/5.49  
% 39.71/5.49  git: date: 2020-06-30 10:37:57 +0100
% 39.71/5.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.71/5.49  git: non_committed_changes: false
% 39.71/5.49  git: last_make_outside_of_git: false
% 39.71/5.49  
% 39.71/5.49  ------ 
% 39.71/5.49  
% 39.71/5.49  ------ Input Options
% 39.71/5.49  
% 39.71/5.49  --out_options                           all
% 39.71/5.49  --tptp_safe_out                         true
% 39.71/5.49  --problem_path                          ""
% 39.71/5.49  --include_path                          ""
% 39.71/5.49  --clausifier                            res/vclausify_rel
% 39.71/5.49  --clausifier_options                    --mode clausify
% 39.71/5.49  --stdin                                 false
% 39.71/5.49  --stats_out                             all
% 39.71/5.49  
% 39.71/5.49  ------ General Options
% 39.71/5.49  
% 39.71/5.49  --fof                                   false
% 39.71/5.49  --time_out_real                         305.
% 39.71/5.49  --time_out_virtual                      -1.
% 39.71/5.49  --symbol_type_check                     false
% 39.71/5.49  --clausify_out                          false
% 39.71/5.49  --sig_cnt_out                           false
% 39.71/5.49  --trig_cnt_out                          false
% 39.71/5.49  --trig_cnt_out_tolerance                1.
% 39.71/5.49  --trig_cnt_out_sk_spl                   false
% 39.71/5.49  --abstr_cl_out                          false
% 39.71/5.49  
% 39.71/5.49  ------ Global Options
% 39.71/5.49  
% 39.71/5.49  --schedule                              default
% 39.71/5.49  --add_important_lit                     false
% 39.71/5.49  --prop_solver_per_cl                    1000
% 39.71/5.49  --min_unsat_core                        false
% 39.71/5.49  --soft_assumptions                      false
% 39.71/5.49  --soft_lemma_size                       3
% 39.71/5.49  --prop_impl_unit_size                   0
% 39.71/5.49  --prop_impl_unit                        []
% 39.71/5.49  --share_sel_clauses                     true
% 39.71/5.49  --reset_solvers                         false
% 39.71/5.49  --bc_imp_inh                            [conj_cone]
% 39.71/5.49  --conj_cone_tolerance                   3.
% 39.71/5.49  --extra_neg_conj                        none
% 39.71/5.49  --large_theory_mode                     true
% 39.71/5.49  --prolific_symb_bound                   200
% 39.71/5.49  --lt_threshold                          2000
% 39.71/5.49  --clause_weak_htbl                      true
% 39.71/5.49  --gc_record_bc_elim                     false
% 39.71/5.49  
% 39.71/5.49  ------ Preprocessing Options
% 39.71/5.49  
% 39.71/5.49  --preprocessing_flag                    true
% 39.71/5.49  --time_out_prep_mult                    0.1
% 39.71/5.49  --splitting_mode                        input
% 39.71/5.49  --splitting_grd                         true
% 39.71/5.49  --splitting_cvd                         false
% 39.71/5.49  --splitting_cvd_svl                     false
% 39.71/5.49  --splitting_nvd                         32
% 39.71/5.49  --sub_typing                            true
% 39.71/5.49  --prep_gs_sim                           true
% 39.71/5.49  --prep_unflatten                        true
% 39.71/5.49  --prep_res_sim                          true
% 39.71/5.49  --prep_upred                            true
% 39.71/5.49  --prep_sem_filter                       exhaustive
% 39.71/5.49  --prep_sem_filter_out                   false
% 39.71/5.49  --pred_elim                             true
% 39.71/5.49  --res_sim_input                         true
% 39.71/5.49  --eq_ax_congr_red                       true
% 39.71/5.49  --pure_diseq_elim                       true
% 39.71/5.49  --brand_transform                       false
% 39.71/5.49  --non_eq_to_eq                          false
% 39.71/5.49  --prep_def_merge                        true
% 39.71/5.49  --prep_def_merge_prop_impl              false
% 39.71/5.49  --prep_def_merge_mbd                    true
% 39.71/5.49  --prep_def_merge_tr_red                 false
% 39.71/5.49  --prep_def_merge_tr_cl                  false
% 39.71/5.49  --smt_preprocessing                     true
% 39.71/5.49  --smt_ac_axioms                         fast
% 39.71/5.49  --preprocessed_out                      false
% 39.71/5.49  --preprocessed_stats                    false
% 39.71/5.49  
% 39.71/5.49  ------ Abstraction refinement Options
% 39.71/5.49  
% 39.71/5.49  --abstr_ref                             []
% 39.71/5.49  --abstr_ref_prep                        false
% 39.71/5.49  --abstr_ref_until_sat                   false
% 39.71/5.49  --abstr_ref_sig_restrict                funpre
% 39.71/5.49  --abstr_ref_af_restrict_to_split_sk     false
% 39.71/5.49  --abstr_ref_under                       []
% 39.71/5.49  
% 39.71/5.49  ------ SAT Options
% 39.71/5.49  
% 39.71/5.49  --sat_mode                              false
% 39.71/5.49  --sat_fm_restart_options                ""
% 39.71/5.49  --sat_gr_def                            false
% 39.71/5.49  --sat_epr_types                         true
% 39.71/5.49  --sat_non_cyclic_types                  false
% 39.71/5.49  --sat_finite_models                     false
% 39.71/5.49  --sat_fm_lemmas                         false
% 39.71/5.49  --sat_fm_prep                           false
% 39.71/5.49  --sat_fm_uc_incr                        true
% 39.71/5.49  --sat_out_model                         small
% 39.71/5.49  --sat_out_clauses                       false
% 39.71/5.49  
% 39.71/5.49  ------ QBF Options
% 39.71/5.49  
% 39.71/5.49  --qbf_mode                              false
% 39.71/5.49  --qbf_elim_univ                         false
% 39.71/5.49  --qbf_dom_inst                          none
% 39.71/5.49  --qbf_dom_pre_inst                      false
% 39.71/5.49  --qbf_sk_in                             false
% 39.71/5.49  --qbf_pred_elim                         true
% 39.71/5.49  --qbf_split                             512
% 39.71/5.49  
% 39.71/5.49  ------ BMC1 Options
% 39.71/5.49  
% 39.71/5.49  --bmc1_incremental                      false
% 39.71/5.49  --bmc1_axioms                           reachable_all
% 39.71/5.49  --bmc1_min_bound                        0
% 39.71/5.49  --bmc1_max_bound                        -1
% 39.71/5.49  --bmc1_max_bound_default                -1
% 39.71/5.49  --bmc1_symbol_reachability              true
% 39.71/5.49  --bmc1_property_lemmas                  false
% 39.71/5.49  --bmc1_k_induction                      false
% 39.71/5.49  --bmc1_non_equiv_states                 false
% 39.71/5.49  --bmc1_deadlock                         false
% 39.71/5.49  --bmc1_ucm                              false
% 39.71/5.49  --bmc1_add_unsat_core                   none
% 39.71/5.49  --bmc1_unsat_core_children              false
% 39.71/5.49  --bmc1_unsat_core_extrapolate_axioms    false
% 39.71/5.49  --bmc1_out_stat                         full
% 39.71/5.49  --bmc1_ground_init                      false
% 39.71/5.49  --bmc1_pre_inst_next_state              false
% 39.71/5.49  --bmc1_pre_inst_state                   false
% 39.71/5.49  --bmc1_pre_inst_reach_state             false
% 39.71/5.49  --bmc1_out_unsat_core                   false
% 39.71/5.49  --bmc1_aig_witness_out                  false
% 39.71/5.49  --bmc1_verbose                          false
% 39.71/5.49  --bmc1_dump_clauses_tptp                false
% 39.71/5.49  --bmc1_dump_unsat_core_tptp             false
% 39.71/5.49  --bmc1_dump_file                        -
% 39.71/5.49  --bmc1_ucm_expand_uc_limit              128
% 39.71/5.49  --bmc1_ucm_n_expand_iterations          6
% 39.71/5.49  --bmc1_ucm_extend_mode                  1
% 39.71/5.49  --bmc1_ucm_init_mode                    2
% 39.71/5.49  --bmc1_ucm_cone_mode                    none
% 39.71/5.49  --bmc1_ucm_reduced_relation_type        0
% 39.71/5.49  --bmc1_ucm_relax_model                  4
% 39.71/5.49  --bmc1_ucm_full_tr_after_sat            true
% 39.71/5.49  --bmc1_ucm_expand_neg_assumptions       false
% 39.71/5.49  --bmc1_ucm_layered_model                none
% 39.71/5.49  --bmc1_ucm_max_lemma_size               10
% 39.71/5.49  
% 39.71/5.49  ------ AIG Options
% 39.71/5.49  
% 39.71/5.49  --aig_mode                              false
% 39.71/5.49  
% 39.71/5.49  ------ Instantiation Options
% 39.71/5.49  
% 39.71/5.49  --instantiation_flag                    true
% 39.71/5.49  --inst_sos_flag                         false
% 39.71/5.49  --inst_sos_phase                        true
% 39.71/5.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.71/5.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.71/5.49  --inst_lit_sel_side                     num_symb
% 39.71/5.49  --inst_solver_per_active                1400
% 39.71/5.49  --inst_solver_calls_frac                1.
% 39.71/5.49  --inst_passive_queue_type               priority_queues
% 39.71/5.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.71/5.49  --inst_passive_queues_freq              [25;2]
% 39.71/5.49  --inst_dismatching                      true
% 39.71/5.49  --inst_eager_unprocessed_to_passive     true
% 39.71/5.49  --inst_prop_sim_given                   true
% 39.71/5.49  --inst_prop_sim_new                     false
% 39.71/5.49  --inst_subs_new                         false
% 39.71/5.49  --inst_eq_res_simp                      false
% 39.71/5.49  --inst_subs_given                       false
% 39.71/5.49  --inst_orphan_elimination               true
% 39.71/5.49  --inst_learning_loop_flag               true
% 39.71/5.49  --inst_learning_start                   3000
% 39.71/5.49  --inst_learning_factor                  2
% 39.71/5.49  --inst_start_prop_sim_after_learn       3
% 39.71/5.49  --inst_sel_renew                        solver
% 39.71/5.49  --inst_lit_activity_flag                true
% 39.71/5.49  --inst_restr_to_given                   false
% 39.71/5.49  --inst_activity_threshold               500
% 39.71/5.49  --inst_out_proof                        true
% 39.71/5.49  
% 39.71/5.49  ------ Resolution Options
% 39.71/5.49  
% 39.71/5.49  --resolution_flag                       true
% 39.71/5.49  --res_lit_sel                           adaptive
% 39.71/5.49  --res_lit_sel_side                      none
% 39.71/5.49  --res_ordering                          kbo
% 39.71/5.49  --res_to_prop_solver                    active
% 39.71/5.49  --res_prop_simpl_new                    false
% 39.71/5.49  --res_prop_simpl_given                  true
% 39.71/5.49  --res_passive_queue_type                priority_queues
% 39.71/5.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.71/5.49  --res_passive_queues_freq               [15;5]
% 39.71/5.49  --res_forward_subs                      full
% 39.71/5.49  --res_backward_subs                     full
% 39.71/5.49  --res_forward_subs_resolution           true
% 39.71/5.49  --res_backward_subs_resolution          true
% 39.71/5.49  --res_orphan_elimination                true
% 39.71/5.49  --res_time_limit                        2.
% 39.71/5.49  --res_out_proof                         true
% 39.71/5.49  
% 39.71/5.49  ------ Superposition Options
% 39.71/5.49  
% 39.71/5.49  --superposition_flag                    true
% 39.71/5.49  --sup_passive_queue_type                priority_queues
% 39.71/5.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.71/5.49  --sup_passive_queues_freq               [8;1;4]
% 39.71/5.49  --demod_completeness_check              fast
% 39.71/5.49  --demod_use_ground                      true
% 39.71/5.49  --sup_to_prop_solver                    passive
% 39.71/5.49  --sup_prop_simpl_new                    true
% 39.71/5.49  --sup_prop_simpl_given                  true
% 39.71/5.49  --sup_fun_splitting                     false
% 39.71/5.49  --sup_smt_interval                      50000
% 39.71/5.49  
% 39.71/5.49  ------ Superposition Simplification Setup
% 39.71/5.49  
% 39.71/5.49  --sup_indices_passive                   []
% 39.71/5.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.71/5.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.71/5.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.71/5.49  --sup_full_triv                         [TrivRules;PropSubs]
% 39.71/5.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.71/5.49  --sup_full_bw                           [BwDemod]
% 39.71/5.49  --sup_immed_triv                        [TrivRules]
% 39.71/5.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.71/5.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.71/5.49  --sup_immed_bw_main                     []
% 39.71/5.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.71/5.49  --sup_input_triv                        [Unflattening;TrivRules]
% 39.71/5.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.71/5.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.71/5.49  
% 39.71/5.49  ------ Combination Options
% 39.71/5.49  
% 39.71/5.49  --comb_res_mult                         3
% 39.71/5.49  --comb_sup_mult                         2
% 39.71/5.49  --comb_inst_mult                        10
% 39.71/5.49  
% 39.71/5.49  ------ Debug Options
% 39.71/5.49  
% 39.71/5.49  --dbg_backtrace                         false
% 39.71/5.49  --dbg_dump_prop_clauses                 false
% 39.71/5.49  --dbg_dump_prop_clauses_file            -
% 39.71/5.49  --dbg_out_stat                          false
% 39.71/5.49  ------ Parsing...
% 39.71/5.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.71/5.49  
% 39.71/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 39.71/5.49  
% 39.71/5.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.71/5.49  
% 39.71/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.71/5.49  ------ Proving...
% 39.71/5.49  ------ Problem Properties 
% 39.71/5.49  
% 39.71/5.49  
% 39.71/5.49  clauses                                 8
% 39.71/5.49  conjectures                             3
% 39.71/5.49  EPR                                     0
% 39.71/5.49  Horn                                    8
% 39.71/5.49  unary                                   6
% 39.71/5.49  binary                                  1
% 39.71/5.49  lits                                    11
% 39.71/5.49  lits eq                                 3
% 39.71/5.49  fd_pure                                 0
% 39.71/5.49  fd_pseudo                               0
% 39.71/5.49  fd_cond                                 0
% 39.71/5.49  fd_pseudo_cond                          0
% 39.71/5.49  AC symbols                              0
% 39.71/5.49  
% 39.71/5.49  ------ Schedule dynamic 5 is on 
% 39.71/5.49  
% 39.71/5.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 39.71/5.49  
% 39.71/5.49  
% 39.71/5.49  ------ 
% 39.71/5.49  Current options:
% 39.71/5.49  ------ 
% 39.71/5.49  
% 39.71/5.49  ------ Input Options
% 39.71/5.49  
% 39.71/5.49  --out_options                           all
% 39.71/5.49  --tptp_safe_out                         true
% 39.71/5.49  --problem_path                          ""
% 39.71/5.49  --include_path                          ""
% 39.71/5.49  --clausifier                            res/vclausify_rel
% 39.71/5.49  --clausifier_options                    --mode clausify
% 39.71/5.49  --stdin                                 false
% 39.71/5.49  --stats_out                             all
% 39.71/5.49  
% 39.71/5.49  ------ General Options
% 39.71/5.49  
% 39.71/5.49  --fof                                   false
% 39.71/5.49  --time_out_real                         305.
% 39.71/5.49  --time_out_virtual                      -1.
% 39.71/5.49  --symbol_type_check                     false
% 39.71/5.49  --clausify_out                          false
% 39.71/5.49  --sig_cnt_out                           false
% 39.71/5.49  --trig_cnt_out                          false
% 39.71/5.49  --trig_cnt_out_tolerance                1.
% 39.71/5.49  --trig_cnt_out_sk_spl                   false
% 39.71/5.49  --abstr_cl_out                          false
% 39.71/5.49  
% 39.71/5.49  ------ Global Options
% 39.71/5.49  
% 39.71/5.49  --schedule                              default
% 39.71/5.49  --add_important_lit                     false
% 39.71/5.49  --prop_solver_per_cl                    1000
% 39.71/5.49  --min_unsat_core                        false
% 39.71/5.49  --soft_assumptions                      false
% 39.71/5.49  --soft_lemma_size                       3
% 39.71/5.49  --prop_impl_unit_size                   0
% 39.71/5.49  --prop_impl_unit                        []
% 39.71/5.49  --share_sel_clauses                     true
% 39.71/5.49  --reset_solvers                         false
% 39.71/5.49  --bc_imp_inh                            [conj_cone]
% 39.71/5.49  --conj_cone_tolerance                   3.
% 39.71/5.49  --extra_neg_conj                        none
% 39.71/5.49  --large_theory_mode                     true
% 39.71/5.49  --prolific_symb_bound                   200
% 39.71/5.49  --lt_threshold                          2000
% 39.71/5.49  --clause_weak_htbl                      true
% 39.71/5.49  --gc_record_bc_elim                     false
% 39.71/5.49  
% 39.71/5.49  ------ Preprocessing Options
% 39.71/5.49  
% 39.71/5.49  --preprocessing_flag                    true
% 39.71/5.49  --time_out_prep_mult                    0.1
% 39.71/5.49  --splitting_mode                        input
% 39.71/5.49  --splitting_grd                         true
% 39.71/5.49  --splitting_cvd                         false
% 39.71/5.49  --splitting_cvd_svl                     false
% 39.71/5.49  --splitting_nvd                         32
% 39.71/5.49  --sub_typing                            true
% 39.71/5.49  --prep_gs_sim                           true
% 39.71/5.49  --prep_unflatten                        true
% 39.71/5.49  --prep_res_sim                          true
% 39.71/5.49  --prep_upred                            true
% 39.71/5.49  --prep_sem_filter                       exhaustive
% 39.71/5.49  --prep_sem_filter_out                   false
% 39.71/5.49  --pred_elim                             true
% 39.71/5.49  --res_sim_input                         true
% 39.71/5.49  --eq_ax_congr_red                       true
% 39.71/5.49  --pure_diseq_elim                       true
% 39.71/5.49  --brand_transform                       false
% 39.71/5.49  --non_eq_to_eq                          false
% 39.71/5.49  --prep_def_merge                        true
% 39.71/5.49  --prep_def_merge_prop_impl              false
% 39.71/5.49  --prep_def_merge_mbd                    true
% 39.71/5.49  --prep_def_merge_tr_red                 false
% 39.71/5.49  --prep_def_merge_tr_cl                  false
% 39.71/5.49  --smt_preprocessing                     true
% 39.71/5.49  --smt_ac_axioms                         fast
% 39.71/5.49  --preprocessed_out                      false
% 39.71/5.49  --preprocessed_stats                    false
% 39.71/5.49  
% 39.71/5.49  ------ Abstraction refinement Options
% 39.71/5.49  
% 39.71/5.49  --abstr_ref                             []
% 39.71/5.49  --abstr_ref_prep                        false
% 39.71/5.49  --abstr_ref_until_sat                   false
% 39.71/5.49  --abstr_ref_sig_restrict                funpre
% 39.71/5.49  --abstr_ref_af_restrict_to_split_sk     false
% 39.71/5.49  --abstr_ref_under                       []
% 39.71/5.49  
% 39.71/5.49  ------ SAT Options
% 39.71/5.49  
% 39.71/5.49  --sat_mode                              false
% 39.71/5.49  --sat_fm_restart_options                ""
% 39.71/5.49  --sat_gr_def                            false
% 39.71/5.49  --sat_epr_types                         true
% 39.71/5.49  --sat_non_cyclic_types                  false
% 39.71/5.49  --sat_finite_models                     false
% 39.71/5.49  --sat_fm_lemmas                         false
% 39.71/5.49  --sat_fm_prep                           false
% 39.71/5.49  --sat_fm_uc_incr                        true
% 39.71/5.49  --sat_out_model                         small
% 39.71/5.49  --sat_out_clauses                       false
% 39.71/5.49  
% 39.71/5.49  ------ QBF Options
% 39.71/5.49  
% 39.71/5.49  --qbf_mode                              false
% 39.71/5.49  --qbf_elim_univ                         false
% 39.71/5.49  --qbf_dom_inst                          none
% 39.71/5.49  --qbf_dom_pre_inst                      false
% 39.71/5.49  --qbf_sk_in                             false
% 39.71/5.49  --qbf_pred_elim                         true
% 39.71/5.49  --qbf_split                             512
% 39.71/5.49  
% 39.71/5.49  ------ BMC1 Options
% 39.71/5.49  
% 39.71/5.49  --bmc1_incremental                      false
% 39.71/5.49  --bmc1_axioms                           reachable_all
% 39.71/5.49  --bmc1_min_bound                        0
% 39.71/5.49  --bmc1_max_bound                        -1
% 39.71/5.49  --bmc1_max_bound_default                -1
% 39.71/5.49  --bmc1_symbol_reachability              true
% 39.71/5.49  --bmc1_property_lemmas                  false
% 39.71/5.49  --bmc1_k_induction                      false
% 39.71/5.49  --bmc1_non_equiv_states                 false
% 39.71/5.49  --bmc1_deadlock                         false
% 39.71/5.49  --bmc1_ucm                              false
% 39.71/5.49  --bmc1_add_unsat_core                   none
% 39.71/5.49  --bmc1_unsat_core_children              false
% 39.71/5.49  --bmc1_unsat_core_extrapolate_axioms    false
% 39.71/5.49  --bmc1_out_stat                         full
% 39.71/5.49  --bmc1_ground_init                      false
% 39.71/5.49  --bmc1_pre_inst_next_state              false
% 39.71/5.49  --bmc1_pre_inst_state                   false
% 39.71/5.49  --bmc1_pre_inst_reach_state             false
% 39.71/5.49  --bmc1_out_unsat_core                   false
% 39.71/5.49  --bmc1_aig_witness_out                  false
% 39.71/5.49  --bmc1_verbose                          false
% 39.71/5.49  --bmc1_dump_clauses_tptp                false
% 39.71/5.49  --bmc1_dump_unsat_core_tptp             false
% 39.71/5.49  --bmc1_dump_file                        -
% 39.71/5.49  --bmc1_ucm_expand_uc_limit              128
% 39.71/5.49  --bmc1_ucm_n_expand_iterations          6
% 39.71/5.49  --bmc1_ucm_extend_mode                  1
% 39.71/5.49  --bmc1_ucm_init_mode                    2
% 39.71/5.49  --bmc1_ucm_cone_mode                    none
% 39.71/5.49  --bmc1_ucm_reduced_relation_type        0
% 39.71/5.49  --bmc1_ucm_relax_model                  4
% 39.71/5.49  --bmc1_ucm_full_tr_after_sat            true
% 39.71/5.49  --bmc1_ucm_expand_neg_assumptions       false
% 39.71/5.49  --bmc1_ucm_layered_model                none
% 39.71/5.49  --bmc1_ucm_max_lemma_size               10
% 39.71/5.49  
% 39.71/5.49  ------ AIG Options
% 39.71/5.49  
% 39.71/5.49  --aig_mode                              false
% 39.71/5.49  
% 39.71/5.49  ------ Instantiation Options
% 39.71/5.49  
% 39.71/5.49  --instantiation_flag                    true
% 39.71/5.49  --inst_sos_flag                         false
% 39.71/5.49  --inst_sos_phase                        true
% 39.71/5.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.71/5.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.71/5.49  --inst_lit_sel_side                     none
% 39.71/5.49  --inst_solver_per_active                1400
% 39.71/5.49  --inst_solver_calls_frac                1.
% 39.71/5.49  --inst_passive_queue_type               priority_queues
% 39.71/5.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.71/5.49  --inst_passive_queues_freq              [25;2]
% 39.71/5.49  --inst_dismatching                      true
% 39.71/5.49  --inst_eager_unprocessed_to_passive     true
% 39.71/5.49  --inst_prop_sim_given                   true
% 39.71/5.49  --inst_prop_sim_new                     false
% 39.71/5.49  --inst_subs_new                         false
% 39.71/5.49  --inst_eq_res_simp                      false
% 39.71/5.49  --inst_subs_given                       false
% 39.71/5.49  --inst_orphan_elimination               true
% 39.71/5.49  --inst_learning_loop_flag               true
% 39.71/5.49  --inst_learning_start                   3000
% 39.71/5.49  --inst_learning_factor                  2
% 39.71/5.49  --inst_start_prop_sim_after_learn       3
% 39.71/5.49  --inst_sel_renew                        solver
% 39.71/5.49  --inst_lit_activity_flag                true
% 39.71/5.49  --inst_restr_to_given                   false
% 39.71/5.49  --inst_activity_threshold               500
% 39.71/5.49  --inst_out_proof                        true
% 39.71/5.49  
% 39.71/5.49  ------ Resolution Options
% 39.71/5.49  
% 39.71/5.49  --resolution_flag                       false
% 39.71/5.49  --res_lit_sel                           adaptive
% 39.71/5.49  --res_lit_sel_side                      none
% 39.71/5.49  --res_ordering                          kbo
% 39.71/5.49  --res_to_prop_solver                    active
% 39.71/5.49  --res_prop_simpl_new                    false
% 39.71/5.49  --res_prop_simpl_given                  true
% 39.71/5.49  --res_passive_queue_type                priority_queues
% 39.71/5.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.71/5.49  --res_passive_queues_freq               [15;5]
% 39.71/5.49  --res_forward_subs                      full
% 39.71/5.49  --res_backward_subs                     full
% 39.71/5.49  --res_forward_subs_resolution           true
% 39.71/5.49  --res_backward_subs_resolution          true
% 39.71/5.49  --res_orphan_elimination                true
% 39.71/5.49  --res_time_limit                        2.
% 39.71/5.49  --res_out_proof                         true
% 39.71/5.49  
% 39.71/5.49  ------ Superposition Options
% 39.71/5.49  
% 39.71/5.49  --superposition_flag                    true
% 39.71/5.49  --sup_passive_queue_type                priority_queues
% 39.71/5.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.71/5.49  --sup_passive_queues_freq               [8;1;4]
% 39.71/5.49  --demod_completeness_check              fast
% 39.71/5.49  --demod_use_ground                      true
% 39.71/5.49  --sup_to_prop_solver                    passive
% 39.71/5.49  --sup_prop_simpl_new                    true
% 39.71/5.49  --sup_prop_simpl_given                  true
% 39.71/5.49  --sup_fun_splitting                     false
% 39.71/5.49  --sup_smt_interval                      50000
% 39.71/5.49  
% 39.71/5.49  ------ Superposition Simplification Setup
% 39.71/5.49  
% 39.71/5.49  --sup_indices_passive                   []
% 39.71/5.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.71/5.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.71/5.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.71/5.49  --sup_full_triv                         [TrivRules;PropSubs]
% 39.71/5.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.71/5.49  --sup_full_bw                           [BwDemod]
% 39.71/5.49  --sup_immed_triv                        [TrivRules]
% 39.71/5.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.71/5.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.71/5.49  --sup_immed_bw_main                     []
% 39.71/5.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.71/5.49  --sup_input_triv                        [Unflattening;TrivRules]
% 39.71/5.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.71/5.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.71/5.49  
% 39.71/5.49  ------ Combination Options
% 39.71/5.49  
% 39.71/5.49  --comb_res_mult                         3
% 39.71/5.49  --comb_sup_mult                         2
% 39.71/5.49  --comb_inst_mult                        10
% 39.71/5.49  
% 39.71/5.49  ------ Debug Options
% 39.71/5.49  
% 39.71/5.49  --dbg_backtrace                         false
% 39.71/5.49  --dbg_dump_prop_clauses                 false
% 39.71/5.49  --dbg_dump_prop_clauses_file            -
% 39.71/5.49  --dbg_out_stat                          false
% 39.71/5.49  
% 39.71/5.49  
% 39.71/5.49  
% 39.71/5.49  
% 39.71/5.49  ------ Proving...
% 39.71/5.49  
% 39.71/5.49  
% 39.71/5.49  % SZS status Theorem for theBenchmark.p
% 39.71/5.49  
% 39.71/5.49  % SZS output start CNFRefutation for theBenchmark.p
% 39.71/5.49  
% 39.71/5.49  fof(f5,axiom,(
% 39.71/5.49    ! [X0,X1,X2] : (k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) & k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2))),
% 39.71/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.71/5.49  
% 39.71/5.49  fof(f20,plain,(
% 39.71/5.49    ( ! [X2,X0,X1] : (k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1))) )),
% 39.71/5.49    inference(cnf_transformation,[],[f5])).
% 39.71/5.49  
% 39.71/5.49  fof(f4,axiom,(
% 39.71/5.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 39.71/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.71/5.49  
% 39.71/5.49  fof(f18,plain,(
% 39.71/5.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 39.71/5.49    inference(cnf_transformation,[],[f4])).
% 39.71/5.49  
% 39.71/5.49  fof(f27,plain,(
% 39.71/5.49    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(X2,k3_tarski(k2_tarski(X0,X1)))) )),
% 39.71/5.49    inference(definition_unfolding,[],[f20,f18,f18])).
% 39.71/5.49  
% 39.71/5.49  fof(f2,axiom,(
% 39.71/5.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 39.71/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.71/5.49  
% 39.71/5.49  fof(f8,plain,(
% 39.71/5.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 39.71/5.49    inference(ennf_transformation,[],[f2])).
% 39.71/5.49  
% 39.71/5.49  fof(f16,plain,(
% 39.71/5.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 39.71/5.49    inference(cnf_transformation,[],[f8])).
% 39.71/5.49  
% 39.71/5.49  fof(f25,plain,(
% 39.71/5.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 39.71/5.49    inference(definition_unfolding,[],[f16,f18])).
% 39.71/5.49  
% 39.71/5.49  fof(f1,axiom,(
% 39.71/5.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 39.71/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.71/5.49  
% 39.71/5.49  fof(f15,plain,(
% 39.71/5.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 39.71/5.49    inference(cnf_transformation,[],[f1])).
% 39.71/5.49  
% 39.71/5.49  fof(f24,plain,(
% 39.71/5.49    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0))) )),
% 39.71/5.49    inference(definition_unfolding,[],[f15,f18,f18])).
% 39.71/5.49  
% 39.71/5.49  fof(f19,plain,(
% 39.71/5.49    ( ! [X2,X0,X1] : (k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2)) )),
% 39.71/5.49    inference(cnf_transformation,[],[f5])).
% 39.71/5.49  
% 39.71/5.49  fof(f28,plain,(
% 39.71/5.49    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) = k2_zfmisc_1(k3_tarski(k2_tarski(X0,X1)),X2)) )),
% 39.71/5.49    inference(definition_unfolding,[],[f19,f18,f18])).
% 39.71/5.49  
% 39.71/5.49  fof(f3,axiom,(
% 39.71/5.49    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 39.71/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.71/5.49  
% 39.71/5.49  fof(f9,plain,(
% 39.71/5.49    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 39.71/5.49    inference(ennf_transformation,[],[f3])).
% 39.71/5.49  
% 39.71/5.49  fof(f10,plain,(
% 39.71/5.49    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 39.71/5.49    inference(flattening,[],[f9])).
% 39.71/5.49  
% 39.71/5.49  fof(f17,plain,(
% 39.71/5.49    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 39.71/5.49    inference(cnf_transformation,[],[f10])).
% 39.71/5.49  
% 39.71/5.49  fof(f26,plain,(
% 39.71/5.49    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X3))) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 39.71/5.49    inference(definition_unfolding,[],[f17,f18,f18])).
% 39.71/5.49  
% 39.71/5.49  fof(f6,conjecture,(
% 39.71/5.49    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 39.71/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.71/5.49  
% 39.71/5.49  fof(f7,negated_conjecture,(
% 39.71/5.49    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 39.71/5.49    inference(negated_conjecture,[],[f6])).
% 39.71/5.49  
% 39.71/5.49  fof(f11,plain,(
% 39.71/5.49    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 39.71/5.49    inference(ennf_transformation,[],[f7])).
% 39.71/5.49  
% 39.71/5.49  fof(f12,plain,(
% 39.71/5.49    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 39.71/5.49    inference(flattening,[],[f11])).
% 39.71/5.49  
% 39.71/5.49  fof(f13,plain,(
% 39.71/5.49    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 39.71/5.49    introduced(choice_axiom,[])).
% 39.71/5.49  
% 39.71/5.49  fof(f14,plain,(
% 39.71/5.49    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 39.71/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f12,f13])).
% 39.71/5.49  
% 39.71/5.49  fof(f23,plain,(
% 39.71/5.49    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 39.71/5.49    inference(cnf_transformation,[],[f14])).
% 39.71/5.49  
% 39.71/5.49  fof(f29,plain,(
% 39.71/5.49    ~r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))),
% 39.71/5.49    inference(definition_unfolding,[],[f23,f18,f18,f18])).
% 39.71/5.49  
% 39.71/5.49  fof(f21,plain,(
% 39.71/5.49    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 39.71/5.49    inference(cnf_transformation,[],[f14])).
% 39.71/5.49  
% 39.71/5.49  fof(f22,plain,(
% 39.71/5.49    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 39.71/5.49    inference(cnf_transformation,[],[f14])).
% 39.71/5.49  
% 39.71/5.49  cnf(c_3,plain,
% 39.71/5.49      ( k3_tarski(k2_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))) = k2_zfmisc_1(X0,k3_tarski(k2_tarski(X1,X2))) ),
% 39.71/5.49      inference(cnf_transformation,[],[f27]) ).
% 39.71/5.49  
% 39.71/5.49  cnf(c_67,plain,
% 39.71/5.49      ( k3_tarski(k2_tarski(k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X0_38,X2_38))) = k2_zfmisc_1(X0_38,k3_tarski(k2_tarski(X1_38,X2_38))) ),
% 39.71/5.49      inference(subtyping,[status(esa)],[c_3]) ).
% 39.71/5.49  
% 39.71/5.49  cnf(c_1,plain,
% 39.71/5.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) ),
% 39.71/5.49      inference(cnf_transformation,[],[f25]) ).
% 39.71/5.49  
% 39.71/5.49  cnf(c_69,plain,
% 39.71/5.49      ( ~ r1_tarski(X0_38,X1_38)
% 39.71/5.49      | r1_tarski(X0_38,k3_tarski(k2_tarski(X2_38,X1_38))) ),
% 39.71/5.49      inference(subtyping,[status(esa)],[c_1]) ).
% 39.71/5.49  
% 39.71/5.49  cnf(c_174,plain,
% 39.71/5.49      ( r1_tarski(X0_38,X1_38) != iProver_top
% 39.71/5.49      | r1_tarski(X0_38,k3_tarski(k2_tarski(X2_38,X1_38))) = iProver_top ),
% 39.71/5.49      inference(predicate_to_equality,[status(thm)],[c_69]) ).
% 39.71/5.49  
% 39.71/5.49  cnf(c_736,plain,
% 39.71/5.49      ( r1_tarski(X0_38,k2_zfmisc_1(X1_38,X2_38)) != iProver_top
% 39.71/5.49      | r1_tarski(X0_38,k2_zfmisc_1(X1_38,k3_tarski(k2_tarski(X3_38,X2_38)))) = iProver_top ),
% 39.71/5.49      inference(superposition,[status(thm)],[c_67,c_174]) ).
% 39.71/5.49  
% 39.71/5.49  cnf(c_0,plain,
% 39.71/5.49      ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.71/5.49      inference(cnf_transformation,[],[f24]) ).
% 39.71/5.49  
% 39.71/5.49  cnf(c_70,plain,
% 39.71/5.49      ( k3_tarski(k2_tarski(X0_38,X1_38)) = k3_tarski(k2_tarski(X1_38,X0_38)) ),
% 39.71/5.49      inference(subtyping,[status(esa)],[c_0]) ).
% 39.71/5.49  
% 39.71/5.49  cnf(c_467,plain,
% 39.71/5.49      ( k3_tarski(k2_tarski(k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X0_38,X2_38))) = k2_zfmisc_1(X0_38,k3_tarski(k2_tarski(X2_38,X1_38))) ),
% 39.71/5.49      inference(superposition,[status(thm)],[c_67,c_70]) ).
% 39.71/5.49  
% 39.71/5.49  cnf(c_1471,plain,
% 39.71/5.49      ( r1_tarski(X0_38,k2_zfmisc_1(X1_38,X2_38)) != iProver_top
% 39.71/5.49      | r1_tarski(X0_38,k2_zfmisc_1(X1_38,k3_tarski(k2_tarski(X2_38,X3_38)))) = iProver_top ),
% 39.71/5.49      inference(superposition,[status(thm)],[c_467,c_174]) ).
% 39.71/5.49  
% 39.71/5.49  cnf(c_4,plain,
% 39.71/5.49      ( k3_tarski(k2_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(k3_tarski(k2_tarski(X0,X2)),X1) ),
% 39.71/5.49      inference(cnf_transformation,[],[f28]) ).
% 39.71/5.49  
% 39.71/5.49  cnf(c_66,plain,
% 39.71/5.49      ( k3_tarski(k2_tarski(k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X2_38,X1_38))) = k2_zfmisc_1(k3_tarski(k2_tarski(X0_38,X2_38)),X1_38) ),
% 39.71/5.49      inference(subtyping,[status(esa)],[c_4]) ).
% 39.71/5.49  
% 39.71/5.49  cnf(c_2,plain,
% 39.71/5.49      ( ~ r1_tarski(X0,X1)
% 39.71/5.49      | ~ r1_tarski(X2,X3)
% 39.71/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X3))) ),
% 39.71/5.49      inference(cnf_transformation,[],[f26]) ).
% 39.71/5.49  
% 39.71/5.49  cnf(c_68,plain,
% 39.71/5.49      ( ~ r1_tarski(X0_38,X1_38)
% 39.71/5.49      | ~ r1_tarski(X2_38,X3_38)
% 39.71/5.49      | r1_tarski(k3_tarski(k2_tarski(X0_38,X2_38)),k3_tarski(k2_tarski(X1_38,X3_38))) ),
% 39.71/5.49      inference(subtyping,[status(esa)],[c_2]) ).
% 39.71/5.49  
% 39.71/5.49  cnf(c_175,plain,
% 39.71/5.49      ( r1_tarski(X0_38,X1_38) != iProver_top
% 39.71/5.49      | r1_tarski(X2_38,X3_38) != iProver_top
% 39.71/5.49      | r1_tarski(k3_tarski(k2_tarski(X0_38,X2_38)),k3_tarski(k2_tarski(X1_38,X3_38))) = iProver_top ),
% 39.71/5.49      inference(predicate_to_equality,[status(thm)],[c_68]) ).
% 39.71/5.49  
% 39.71/5.49  cnf(c_937,plain,
% 39.71/5.49      ( r1_tarski(X0_38,k2_zfmisc_1(X1_38,X2_38)) != iProver_top
% 39.71/5.49      | r1_tarski(X3_38,k2_zfmisc_1(X4_38,X2_38)) != iProver_top
% 39.71/5.49      | r1_tarski(k3_tarski(k2_tarski(X0_38,X3_38)),k2_zfmisc_1(k3_tarski(k2_tarski(X1_38,X4_38)),X2_38)) = iProver_top ),
% 39.71/5.49      inference(superposition,[status(thm)],[c_66,c_175]) ).
% 39.71/5.49  
% 39.71/5.49  cnf(c_5,negated_conjecture,
% 39.71/5.49      ( ~ r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) ),
% 39.71/5.49      inference(cnf_transformation,[],[f29]) ).
% 39.71/5.49  
% 39.71/5.49  cnf(c_65,negated_conjecture,
% 39.71/5.49      ( ~ r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) ),
% 39.71/5.49      inference(subtyping,[status(esa)],[c_5]) ).
% 39.71/5.49  
% 39.71/5.49  cnf(c_176,plain,
% 39.71/5.49      ( r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top ),
% 39.71/5.49      inference(predicate_to_equality,[status(thm)],[c_65]) ).
% 39.71/5.49  
% 39.71/5.49  cnf(c_111088,plain,
% 39.71/5.49      ( r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top
% 39.71/5.49      | r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top ),
% 39.71/5.49      inference(superposition,[status(thm)],[c_937,c_176]) ).
% 39.71/5.49  
% 39.71/5.49  cnf(c_122816,plain,
% 39.71/5.49      ( r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top
% 39.71/5.49      | r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) != iProver_top ),
% 39.71/5.49      inference(superposition,[status(thm)],[c_1471,c_111088]) ).
% 39.71/5.49  
% 39.71/5.49  cnf(c_7,negated_conjecture,
% 39.71/5.49      ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
% 39.71/5.49      inference(cnf_transformation,[],[f21]) ).
% 39.71/5.49  
% 39.71/5.49  cnf(c_8,plain,
% 39.71/5.49      ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 39.71/5.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 39.71/5.49  
% 39.71/5.49  cnf(c_122841,plain,
% 39.71/5.49      ( r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top ),
% 39.71/5.49      inference(global_propositional_subsumption,
% 39.71/5.49                [status(thm)],
% 39.71/5.49                [c_122816,c_8]) ).
% 39.71/5.49  
% 39.71/5.49  cnf(c_122847,plain,
% 39.71/5.49      ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) != iProver_top ),
% 39.71/5.49      inference(superposition,[status(thm)],[c_736,c_122841]) ).
% 39.71/5.49  
% 39.71/5.49  cnf(c_6,negated_conjecture,
% 39.71/5.49      ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
% 39.71/5.49      inference(cnf_transformation,[],[f22]) ).
% 39.71/5.49  
% 39.71/5.49  cnf(c_9,plain,
% 39.71/5.49      ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 39.71/5.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 39.71/5.49  
% 39.71/5.49  cnf(contradiction,plain,
% 39.71/5.49      ( $false ),
% 39.71/5.49      inference(minisat,[status(thm)],[c_122847,c_9]) ).
% 39.71/5.49  
% 39.71/5.49  
% 39.71/5.49  % SZS output end CNFRefutation for theBenchmark.p
% 39.71/5.49  
% 39.71/5.49  ------                               Statistics
% 39.71/5.49  
% 39.71/5.49  ------ General
% 39.71/5.49  
% 39.71/5.49  abstr_ref_over_cycles:                  0
% 39.71/5.49  abstr_ref_under_cycles:                 0
% 39.71/5.49  gc_basic_clause_elim:                   0
% 39.71/5.49  forced_gc_time:                         0
% 39.71/5.49  parsing_time:                           0.008
% 39.71/5.49  unif_index_cands_time:                  0.
% 39.71/5.49  unif_index_add_time:                    0.
% 39.71/5.49  orderings_time:                         0.
% 39.71/5.49  out_proof_time:                         0.014
% 39.71/5.49  total_time:                             4.962
% 39.71/5.49  num_of_symbols:                         43
% 39.71/5.49  num_of_terms:                           209373
% 39.71/5.49  
% 39.71/5.49  ------ Preprocessing
% 39.71/5.49  
% 39.71/5.49  num_of_splits:                          0
% 39.71/5.49  num_of_split_atoms:                     0
% 39.71/5.49  num_of_reused_defs:                     0
% 39.71/5.49  num_eq_ax_congr_red:                    0
% 39.71/5.49  num_of_sem_filtered_clauses:            1
% 39.71/5.49  num_of_subtypes:                        2
% 39.71/5.49  monotx_restored_types:                  0
% 39.71/5.49  sat_num_of_epr_types:                   0
% 39.71/5.49  sat_num_of_non_cyclic_types:            0
% 39.71/5.49  sat_guarded_non_collapsed_types:        0
% 39.71/5.49  num_pure_diseq_elim:                    0
% 39.71/5.49  simp_replaced_by:                       0
% 39.71/5.49  res_preprocessed:                       39
% 39.71/5.49  prep_upred:                             0
% 39.71/5.49  prep_unflattend:                        0
% 39.71/5.49  smt_new_axioms:                         0
% 39.71/5.49  pred_elim_cands:                        1
% 39.71/5.49  pred_elim:                              0
% 39.71/5.49  pred_elim_cl:                           0
% 39.71/5.49  pred_elim_cycles:                       1
% 39.71/5.49  merged_defs:                            0
% 39.71/5.49  merged_defs_ncl:                        0
% 39.71/5.49  bin_hyper_res:                          0
% 39.71/5.49  prep_cycles:                            3
% 39.71/5.49  pred_elim_time:                         0.
% 39.71/5.49  splitting_time:                         0.
% 39.71/5.49  sem_filter_time:                        0.
% 39.71/5.49  monotx_time:                            0.
% 39.71/5.49  subtype_inf_time:                       0.
% 39.71/5.49  
% 39.71/5.49  ------ Problem properties
% 39.71/5.49  
% 39.71/5.49  clauses:                                8
% 39.71/5.49  conjectures:                            3
% 39.71/5.49  epr:                                    0
% 39.71/5.49  horn:                                   8
% 39.71/5.49  ground:                                 3
% 39.71/5.49  unary:                                  6
% 39.71/5.49  binary:                                 1
% 39.71/5.49  lits:                                   11
% 39.71/5.49  lits_eq:                                3
% 39.71/5.49  fd_pure:                                0
% 39.71/5.49  fd_pseudo:                              0
% 39.71/5.49  fd_cond:                                0
% 39.71/5.49  fd_pseudo_cond:                         0
% 39.71/5.49  ac_symbols:                             0
% 39.71/5.49  
% 39.71/5.49  ------ Propositional Solver
% 39.71/5.49  
% 39.71/5.49  prop_solver_calls:                      41
% 39.71/5.49  prop_fast_solver_calls:                 298
% 39.71/5.49  smt_solver_calls:                       0
% 39.71/5.49  smt_fast_solver_calls:                  0
% 39.71/5.49  prop_num_of_clauses:                    40606
% 39.71/5.49  prop_preprocess_simplified:             8955
% 39.71/5.49  prop_fo_subsumed:                       3
% 39.71/5.49  prop_solver_time:                       0.
% 39.71/5.49  smt_solver_time:                        0.
% 39.71/5.49  smt_fast_solver_time:                   0.
% 39.71/5.49  prop_fast_solver_time:                  0.
% 39.71/5.49  prop_unsat_core_time:                   0.003
% 39.71/5.49  
% 39.71/5.49  ------ QBF
% 39.71/5.49  
% 39.71/5.49  qbf_q_res:                              0
% 39.71/5.49  qbf_num_tautologies:                    0
% 39.71/5.49  qbf_prep_cycles:                        0
% 39.71/5.49  
% 39.71/5.49  ------ BMC1
% 39.71/5.49  
% 39.71/5.49  bmc1_current_bound:                     -1
% 39.71/5.49  bmc1_last_solved_bound:                 -1
% 39.71/5.49  bmc1_unsat_core_size:                   -1
% 39.71/5.49  bmc1_unsat_core_parents_size:           -1
% 39.71/5.49  bmc1_merge_next_fun:                    0
% 39.71/5.49  bmc1_unsat_core_clauses_time:           0.
% 39.71/5.49  
% 39.71/5.49  ------ Instantiation
% 39.71/5.49  
% 39.71/5.49  inst_num_of_clauses:                    791
% 39.71/5.49  inst_num_in_passive:                    132
% 39.71/5.49  inst_num_in_active:                     651
% 39.71/5.49  inst_num_in_unprocessed:                8
% 39.71/5.49  inst_num_of_loops:                      670
% 39.71/5.49  inst_num_of_learning_restarts:          0
% 39.71/5.49  inst_num_moves_active_passive:          17
% 39.71/5.49  inst_lit_activity:                      0
% 39.71/5.49  inst_lit_activity_moves:                1
% 39.71/5.49  inst_num_tautologies:                   0
% 39.71/5.49  inst_num_prop_implied:                  0
% 39.71/5.49  inst_num_existing_simplified:           0
% 39.71/5.49  inst_num_eq_res_simplified:             0
% 39.71/5.49  inst_num_child_elim:                    0
% 39.71/5.49  inst_num_of_dismatching_blockings:      232
% 39.71/5.49  inst_num_of_non_proper_insts:           494
% 39.71/5.49  inst_num_of_duplicates:                 0
% 39.71/5.49  inst_inst_num_from_inst_to_res:         0
% 39.71/5.49  inst_dismatching_checking_time:         0.
% 39.71/5.49  
% 39.71/5.49  ------ Resolution
% 39.71/5.49  
% 39.71/5.49  res_num_of_clauses:                     0
% 39.71/5.49  res_num_in_passive:                     0
% 39.71/5.49  res_num_in_active:                      0
% 39.71/5.49  res_num_of_loops:                       42
% 39.71/5.49  res_forward_subset_subsumed:            8
% 39.71/5.49  res_backward_subset_subsumed:           0
% 39.71/5.49  res_forward_subsumed:                   0
% 39.71/5.49  res_backward_subsumed:                  0
% 39.71/5.49  res_forward_subsumption_resolution:     0
% 39.71/5.49  res_backward_subsumption_resolution:    0
% 39.71/5.49  res_clause_to_clause_subsumption:       381025
% 39.71/5.49  res_orphan_elimination:                 0
% 39.71/5.49  res_tautology_del:                      30
% 39.71/5.49  res_num_eq_res_simplified:              0
% 39.71/5.49  res_num_sel_changes:                    0
% 39.71/5.49  res_moves_from_active_to_pass:          0
% 39.71/5.49  
% 39.71/5.49  ------ Superposition
% 39.71/5.49  
% 39.71/5.49  sup_time_total:                         0.
% 39.71/5.49  sup_time_generating:                    0.
% 39.71/5.49  sup_time_sim_full:                      0.
% 39.71/5.49  sup_time_sim_immed:                     0.
% 39.71/5.49  
% 39.71/5.49  sup_num_of_clauses:                     18967
% 39.71/5.49  sup_num_in_active:                      132
% 39.71/5.49  sup_num_in_passive:                     18835
% 39.71/5.49  sup_num_of_loops:                       132
% 39.71/5.49  sup_fw_superposition:                   25105
% 39.71/5.49  sup_bw_superposition:                   20138
% 39.71/5.49  sup_immediate_simplified:               8267
% 39.71/5.49  sup_given_eliminated:                   0
% 39.71/5.49  comparisons_done:                       0
% 39.71/5.49  comparisons_avoided:                    0
% 39.71/5.49  
% 39.71/5.49  ------ Simplifications
% 39.71/5.49  
% 39.71/5.49  
% 39.71/5.49  sim_fw_subset_subsumed:                 0
% 39.71/5.49  sim_bw_subset_subsumed:                 2
% 39.71/5.49  sim_fw_subsumed:                        742
% 39.71/5.49  sim_bw_subsumed:                        197
% 39.71/5.49  sim_fw_subsumption_res:                 0
% 39.71/5.49  sim_bw_subsumption_res:                 0
% 39.71/5.49  sim_tautology_del:                      0
% 39.71/5.49  sim_eq_tautology_del:                   261
% 39.71/5.49  sim_eq_res_simp:                        0
% 39.71/5.49  sim_fw_demodulated:                     8581
% 39.71/5.49  sim_bw_demodulated:                     189
% 39.71/5.49  sim_light_normalised:                   349
% 39.71/5.49  sim_joinable_taut:                      0
% 39.71/5.49  sim_joinable_simp:                      0
% 39.71/5.49  sim_ac_normalised:                      0
% 39.71/5.49  sim_smt_subsumption:                    0
% 39.71/5.49  
%------------------------------------------------------------------------------
