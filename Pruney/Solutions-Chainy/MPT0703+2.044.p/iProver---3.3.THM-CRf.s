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
% DateTime   : Thu Dec  3 11:52:21 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 125 expanded)
%              Number of clauses        :   36 (  42 expanded)
%              Number of leaves         :    8 (  25 expanded)
%              Depth                    :   16
%              Number of atoms          :  160 ( 380 expanded)
%              Number of equality atoms :   66 (  94 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k2_relat_1(X2))
        & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_tarski(sK0,k2_relat_1(sK2))
      & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f29,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f21,f24])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f30,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f20,f24])).

fof(f31,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_9,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_403,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_407,plain,
    ( k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_986,plain,
    ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1))
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_403,c_407])).

cnf(c_10,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_11,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2357,plain,
    ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_986,c_11])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_404,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_412,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_777,plain,
    ( k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_404,c_412])).

cnf(c_2367,plain,
    ( k10_relat_1(sK2,k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2357,c_777])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_408,plain,
    ( k10_relat_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5206,plain,
    ( k6_subset_1(sK0,sK1) = k1_xboole_0
    | r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2367,c_408])).

cnf(c_5518,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2)) != iProver_top
    | k6_subset_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5206,c_11])).

cnf(c_5519,plain,
    ( k6_subset_1(sK0,sK1) = k1_xboole_0
    | r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5518])).

cnf(c_7,negated_conjecture,
    ( r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_405,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_409,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_410,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_859,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k6_subset_1(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_409,c_410])).

cnf(c_1650,plain,
    ( k6_subset_1(k6_subset_1(X0,X1),X2) = k1_xboole_0
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_859,c_412])).

cnf(c_2627,plain,
    ( k6_subset_1(k6_subset_1(sK0,X0),k2_relat_1(sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_405,c_1650])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_411,plain,
    ( k6_subset_1(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3022,plain,
    ( r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2627,c_411])).

cnf(c_5524,plain,
    ( k6_subset_1(sK0,sK1) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5519,c_3022])).

cnf(c_5533,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5524,c_411])).

cnf(c_6,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_15,plain,
    ( r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5533,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:31:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.82/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/0.98  
% 3.82/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.82/0.98  
% 3.82/0.98  ------  iProver source info
% 3.82/0.98  
% 3.82/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.82/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.82/0.98  git: non_committed_changes: false
% 3.82/0.98  git: last_make_outside_of_git: false
% 3.82/0.98  
% 3.82/0.98  ------ 
% 3.82/0.98  
% 3.82/0.98  ------ Input Options
% 3.82/0.98  
% 3.82/0.98  --out_options                           all
% 3.82/0.98  --tptp_safe_out                         true
% 3.82/0.98  --problem_path                          ""
% 3.82/0.98  --include_path                          ""
% 3.82/0.98  --clausifier                            res/vclausify_rel
% 3.82/0.98  --clausifier_options                    --mode clausify
% 3.82/0.98  --stdin                                 false
% 3.82/0.98  --stats_out                             sel
% 3.82/0.98  
% 3.82/0.98  ------ General Options
% 3.82/0.98  
% 3.82/0.98  --fof                                   false
% 3.82/0.98  --time_out_real                         604.99
% 3.82/0.98  --time_out_virtual                      -1.
% 3.82/0.98  --symbol_type_check                     false
% 3.82/0.98  --clausify_out                          false
% 3.82/0.98  --sig_cnt_out                           false
% 3.82/0.98  --trig_cnt_out                          false
% 3.82/0.98  --trig_cnt_out_tolerance                1.
% 3.82/0.98  --trig_cnt_out_sk_spl                   false
% 3.82/0.98  --abstr_cl_out                          false
% 3.82/0.98  
% 3.82/0.98  ------ Global Options
% 3.82/0.98  
% 3.82/0.98  --schedule                              none
% 3.82/0.98  --add_important_lit                     false
% 3.82/0.98  --prop_solver_per_cl                    1000
% 3.82/0.98  --min_unsat_core                        false
% 3.82/0.98  --soft_assumptions                      false
% 3.82/0.98  --soft_lemma_size                       3
% 3.82/0.98  --prop_impl_unit_size                   0
% 3.82/0.98  --prop_impl_unit                        []
% 3.82/0.98  --share_sel_clauses                     true
% 3.82/0.98  --reset_solvers                         false
% 3.82/0.98  --bc_imp_inh                            [conj_cone]
% 3.82/0.98  --conj_cone_tolerance                   3.
% 3.82/0.98  --extra_neg_conj                        none
% 3.82/0.98  --large_theory_mode                     true
% 3.82/0.98  --prolific_symb_bound                   200
% 3.82/0.98  --lt_threshold                          2000
% 3.82/0.98  --clause_weak_htbl                      true
% 3.82/0.98  --gc_record_bc_elim                     false
% 3.82/0.98  
% 3.82/0.98  ------ Preprocessing Options
% 3.82/0.98  
% 3.82/0.98  --preprocessing_flag                    true
% 3.82/0.98  --time_out_prep_mult                    0.1
% 3.82/0.98  --splitting_mode                        input
% 3.82/0.98  --splitting_grd                         true
% 3.82/0.98  --splitting_cvd                         false
% 3.82/0.98  --splitting_cvd_svl                     false
% 3.82/0.98  --splitting_nvd                         32
% 3.82/0.98  --sub_typing                            true
% 3.82/0.98  --prep_gs_sim                           false
% 3.82/0.98  --prep_unflatten                        true
% 3.82/0.98  --prep_res_sim                          true
% 3.82/0.98  --prep_upred                            true
% 3.82/0.98  --prep_sem_filter                       exhaustive
% 3.82/0.98  --prep_sem_filter_out                   false
% 3.82/0.98  --pred_elim                             false
% 3.82/0.98  --res_sim_input                         true
% 3.82/0.98  --eq_ax_congr_red                       true
% 3.82/0.98  --pure_diseq_elim                       true
% 3.82/0.98  --brand_transform                       false
% 3.82/0.98  --non_eq_to_eq                          false
% 3.82/0.98  --prep_def_merge                        true
% 3.82/0.98  --prep_def_merge_prop_impl              false
% 3.82/0.98  --prep_def_merge_mbd                    true
% 3.82/0.98  --prep_def_merge_tr_red                 false
% 3.82/0.98  --prep_def_merge_tr_cl                  false
% 3.82/0.98  --smt_preprocessing                     true
% 3.82/0.98  --smt_ac_axioms                         fast
% 3.82/0.98  --preprocessed_out                      false
% 3.82/0.98  --preprocessed_stats                    false
% 3.82/0.98  
% 3.82/0.98  ------ Abstraction refinement Options
% 3.82/0.98  
% 3.82/0.98  --abstr_ref                             []
% 3.82/0.98  --abstr_ref_prep                        false
% 3.82/0.98  --abstr_ref_until_sat                   false
% 3.82/0.98  --abstr_ref_sig_restrict                funpre
% 3.82/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.82/0.98  --abstr_ref_under                       []
% 3.82/0.98  
% 3.82/0.98  ------ SAT Options
% 3.82/0.98  
% 3.82/0.98  --sat_mode                              false
% 3.82/0.98  --sat_fm_restart_options                ""
% 3.82/0.98  --sat_gr_def                            false
% 3.82/0.98  --sat_epr_types                         true
% 3.82/0.98  --sat_non_cyclic_types                  false
% 3.82/0.98  --sat_finite_models                     false
% 3.82/0.98  --sat_fm_lemmas                         false
% 3.82/0.98  --sat_fm_prep                           false
% 3.82/0.98  --sat_fm_uc_incr                        true
% 3.82/0.98  --sat_out_model                         small
% 3.82/0.98  --sat_out_clauses                       false
% 3.82/0.98  
% 3.82/0.98  ------ QBF Options
% 3.82/0.98  
% 3.82/0.98  --qbf_mode                              false
% 3.82/0.98  --qbf_elim_univ                         false
% 3.82/0.98  --qbf_dom_inst                          none
% 3.82/0.98  --qbf_dom_pre_inst                      false
% 3.82/0.98  --qbf_sk_in                             false
% 3.82/0.98  --qbf_pred_elim                         true
% 3.82/0.98  --qbf_split                             512
% 3.82/0.98  
% 3.82/0.98  ------ BMC1 Options
% 3.82/0.98  
% 3.82/0.98  --bmc1_incremental                      false
% 3.82/0.98  --bmc1_axioms                           reachable_all
% 3.82/0.98  --bmc1_min_bound                        0
% 3.82/0.98  --bmc1_max_bound                        -1
% 3.82/0.98  --bmc1_max_bound_default                -1
% 3.82/0.98  --bmc1_symbol_reachability              true
% 3.82/0.98  --bmc1_property_lemmas                  false
% 3.82/0.98  --bmc1_k_induction                      false
% 3.82/0.98  --bmc1_non_equiv_states                 false
% 3.82/0.98  --bmc1_deadlock                         false
% 3.82/0.98  --bmc1_ucm                              false
% 3.82/0.98  --bmc1_add_unsat_core                   none
% 3.82/0.98  --bmc1_unsat_core_children              false
% 3.82/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.82/0.98  --bmc1_out_stat                         full
% 3.82/0.98  --bmc1_ground_init                      false
% 3.82/0.98  --bmc1_pre_inst_next_state              false
% 3.82/0.98  --bmc1_pre_inst_state                   false
% 3.82/0.98  --bmc1_pre_inst_reach_state             false
% 3.82/0.98  --bmc1_out_unsat_core                   false
% 3.82/0.98  --bmc1_aig_witness_out                  false
% 3.82/0.98  --bmc1_verbose                          false
% 3.82/0.98  --bmc1_dump_clauses_tptp                false
% 3.82/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.82/0.98  --bmc1_dump_file                        -
% 3.82/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.82/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.82/0.98  --bmc1_ucm_extend_mode                  1
% 3.82/0.98  --bmc1_ucm_init_mode                    2
% 3.82/0.98  --bmc1_ucm_cone_mode                    none
% 3.82/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.82/0.98  --bmc1_ucm_relax_model                  4
% 3.82/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.82/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.82/0.98  --bmc1_ucm_layered_model                none
% 3.82/0.98  --bmc1_ucm_max_lemma_size               10
% 3.82/0.98  
% 3.82/0.98  ------ AIG Options
% 3.82/0.98  
% 3.82/0.98  --aig_mode                              false
% 3.82/0.98  
% 3.82/0.98  ------ Instantiation Options
% 3.82/0.98  
% 3.82/0.98  --instantiation_flag                    true
% 3.82/0.98  --inst_sos_flag                         false
% 3.82/0.98  --inst_sos_phase                        true
% 3.82/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.82/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.82/0.98  --inst_lit_sel_side                     num_symb
% 3.82/0.98  --inst_solver_per_active                1400
% 3.82/0.98  --inst_solver_calls_frac                1.
% 3.82/0.98  --inst_passive_queue_type               priority_queues
% 3.82/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.82/0.98  --inst_passive_queues_freq              [25;2]
% 3.82/0.98  --inst_dismatching                      true
% 3.82/0.98  --inst_eager_unprocessed_to_passive     true
% 3.82/0.98  --inst_prop_sim_given                   true
% 3.82/0.98  --inst_prop_sim_new                     false
% 3.82/0.98  --inst_subs_new                         false
% 3.82/0.98  --inst_eq_res_simp                      false
% 3.82/0.98  --inst_subs_given                       false
% 3.82/0.98  --inst_orphan_elimination               true
% 3.82/0.98  --inst_learning_loop_flag               true
% 3.82/0.98  --inst_learning_start                   3000
% 3.82/0.98  --inst_learning_factor                  2
% 3.82/0.98  --inst_start_prop_sim_after_learn       3
% 3.82/0.98  --inst_sel_renew                        solver
% 3.82/0.98  --inst_lit_activity_flag                true
% 3.82/0.98  --inst_restr_to_given                   false
% 3.82/0.98  --inst_activity_threshold               500
% 3.82/0.98  --inst_out_proof                        true
% 3.82/0.98  
% 3.82/0.98  ------ Resolution Options
% 3.82/0.98  
% 3.82/0.98  --resolution_flag                       true
% 3.82/0.98  --res_lit_sel                           adaptive
% 3.82/0.98  --res_lit_sel_side                      none
% 3.82/0.98  --res_ordering                          kbo
% 3.82/0.98  --res_to_prop_solver                    active
% 3.82/0.98  --res_prop_simpl_new                    false
% 3.82/0.98  --res_prop_simpl_given                  true
% 3.82/0.98  --res_passive_queue_type                priority_queues
% 3.82/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.82/0.98  --res_passive_queues_freq               [15;5]
% 3.82/0.98  --res_forward_subs                      full
% 3.82/0.98  --res_backward_subs                     full
% 3.82/0.98  --res_forward_subs_resolution           true
% 3.82/0.98  --res_backward_subs_resolution          true
% 3.82/0.98  --res_orphan_elimination                true
% 3.82/0.98  --res_time_limit                        2.
% 3.82/0.98  --res_out_proof                         true
% 3.82/0.98  
% 3.82/0.98  ------ Superposition Options
% 3.82/0.98  
% 3.82/0.98  --superposition_flag                    true
% 3.82/0.98  --sup_passive_queue_type                priority_queues
% 3.82/0.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.82/0.98  --sup_passive_queues_freq               [1;4]
% 3.82/0.98  --demod_completeness_check              fast
% 3.82/0.98  --demod_use_ground                      true
% 3.82/0.98  --sup_to_prop_solver                    passive
% 3.82/0.98  --sup_prop_simpl_new                    true
% 3.82/0.98  --sup_prop_simpl_given                  true
% 3.82/0.98  --sup_fun_splitting                     false
% 3.82/0.98  --sup_smt_interval                      50000
% 3.82/0.98  
% 3.82/0.98  ------ Superposition Simplification Setup
% 3.82/0.98  
% 3.82/0.98  --sup_indices_passive                   []
% 3.82/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.82/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.82/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.82/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.82/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.82/0.98  --sup_full_bw                           [BwDemod]
% 3.82/0.98  --sup_immed_triv                        [TrivRules]
% 3.82/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.82/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.82/0.98  --sup_immed_bw_main                     []
% 3.82/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.82/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.82/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.82/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.82/0.98  
% 3.82/0.98  ------ Combination Options
% 3.82/0.98  
% 3.82/0.98  --comb_res_mult                         3
% 3.82/0.98  --comb_sup_mult                         2
% 3.82/0.98  --comb_inst_mult                        10
% 3.82/0.98  
% 3.82/0.98  ------ Debug Options
% 3.82/0.98  
% 3.82/0.98  --dbg_backtrace                         false
% 3.82/0.98  --dbg_dump_prop_clauses                 false
% 3.82/0.98  --dbg_dump_prop_clauses_file            -
% 3.82/0.98  --dbg_out_stat                          false
% 3.82/0.98  ------ Parsing...
% 3.82/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.82/0.98  
% 3.82/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.82/0.98  
% 3.82/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.82/0.98  
% 3.82/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.82/0.98  ------ Proving...
% 3.82/0.98  ------ Problem Properties 
% 3.82/0.98  
% 3.82/0.98  
% 3.82/0.98  clauses                                 11
% 3.82/0.98  conjectures                             5
% 3.82/0.98  EPR                                     4
% 3.82/0.98  Horn                                    11
% 3.82/0.98  unary                                   6
% 3.82/0.98  binary                                  2
% 3.82/0.98  lits                                    20
% 3.82/0.98  lits eq                                 5
% 3.82/0.98  fd_pure                                 0
% 3.82/0.98  fd_pseudo                               0
% 3.82/0.98  fd_cond                                 1
% 3.82/0.98  fd_pseudo_cond                          0
% 3.82/0.98  AC symbols                              0
% 3.82/0.98  
% 3.82/0.98  ------ Input Options Time Limit: Unbounded
% 3.82/0.98  
% 3.82/0.98  
% 3.82/0.98  ------ 
% 3.82/0.98  Current options:
% 3.82/0.98  ------ 
% 3.82/0.98  
% 3.82/0.98  ------ Input Options
% 3.82/0.98  
% 3.82/0.98  --out_options                           all
% 3.82/0.98  --tptp_safe_out                         true
% 3.82/0.98  --problem_path                          ""
% 3.82/0.98  --include_path                          ""
% 3.82/0.98  --clausifier                            res/vclausify_rel
% 3.82/0.98  --clausifier_options                    --mode clausify
% 3.82/0.98  --stdin                                 false
% 3.82/0.98  --stats_out                             sel
% 3.82/0.98  
% 3.82/0.98  ------ General Options
% 3.82/0.98  
% 3.82/0.98  --fof                                   false
% 3.82/0.98  --time_out_real                         604.99
% 3.82/0.98  --time_out_virtual                      -1.
% 3.82/0.98  --symbol_type_check                     false
% 3.82/0.98  --clausify_out                          false
% 3.82/0.98  --sig_cnt_out                           false
% 3.82/0.98  --trig_cnt_out                          false
% 3.82/0.98  --trig_cnt_out_tolerance                1.
% 3.82/0.98  --trig_cnt_out_sk_spl                   false
% 3.82/0.98  --abstr_cl_out                          false
% 3.82/0.98  
% 3.82/0.98  ------ Global Options
% 3.82/0.98  
% 3.82/0.98  --schedule                              none
% 3.82/0.98  --add_important_lit                     false
% 3.82/0.98  --prop_solver_per_cl                    1000
% 3.82/0.98  --min_unsat_core                        false
% 3.82/0.98  --soft_assumptions                      false
% 3.82/0.98  --soft_lemma_size                       3
% 3.82/0.98  --prop_impl_unit_size                   0
% 3.82/0.98  --prop_impl_unit                        []
% 3.82/0.98  --share_sel_clauses                     true
% 3.82/0.98  --reset_solvers                         false
% 3.82/0.98  --bc_imp_inh                            [conj_cone]
% 3.82/0.98  --conj_cone_tolerance                   3.
% 3.82/0.98  --extra_neg_conj                        none
% 3.82/0.98  --large_theory_mode                     true
% 3.82/0.98  --prolific_symb_bound                   200
% 3.82/0.98  --lt_threshold                          2000
% 3.82/0.98  --clause_weak_htbl                      true
% 3.82/0.98  --gc_record_bc_elim                     false
% 3.82/0.98  
% 3.82/0.98  ------ Preprocessing Options
% 3.82/0.98  
% 3.82/0.98  --preprocessing_flag                    true
% 3.82/0.98  --time_out_prep_mult                    0.1
% 3.82/0.98  --splitting_mode                        input
% 3.82/0.98  --splitting_grd                         true
% 3.82/0.98  --splitting_cvd                         false
% 3.82/0.98  --splitting_cvd_svl                     false
% 3.82/0.98  --splitting_nvd                         32
% 3.82/0.98  --sub_typing                            true
% 3.82/0.98  --prep_gs_sim                           false
% 3.82/0.98  --prep_unflatten                        true
% 3.82/0.98  --prep_res_sim                          true
% 3.82/0.98  --prep_upred                            true
% 3.82/0.98  --prep_sem_filter                       exhaustive
% 3.82/0.98  --prep_sem_filter_out                   false
% 3.82/0.98  --pred_elim                             false
% 3.82/0.98  --res_sim_input                         true
% 3.82/0.98  --eq_ax_congr_red                       true
% 3.82/0.98  --pure_diseq_elim                       true
% 3.82/0.98  --brand_transform                       false
% 3.82/0.98  --non_eq_to_eq                          false
% 3.82/0.98  --prep_def_merge                        true
% 3.82/0.98  --prep_def_merge_prop_impl              false
% 3.82/0.98  --prep_def_merge_mbd                    true
% 3.82/0.98  --prep_def_merge_tr_red                 false
% 3.82/0.98  --prep_def_merge_tr_cl                  false
% 3.82/0.98  --smt_preprocessing                     true
% 3.82/0.98  --smt_ac_axioms                         fast
% 3.82/0.98  --preprocessed_out                      false
% 3.82/0.98  --preprocessed_stats                    false
% 3.82/0.98  
% 3.82/0.98  ------ Abstraction refinement Options
% 3.82/0.98  
% 3.82/0.98  --abstr_ref                             []
% 3.82/0.98  --abstr_ref_prep                        false
% 3.82/0.98  --abstr_ref_until_sat                   false
% 3.82/0.98  --abstr_ref_sig_restrict                funpre
% 3.82/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.82/0.98  --abstr_ref_under                       []
% 3.82/0.98  
% 3.82/0.98  ------ SAT Options
% 3.82/0.98  
% 3.82/0.98  --sat_mode                              false
% 3.82/0.98  --sat_fm_restart_options                ""
% 3.82/0.98  --sat_gr_def                            false
% 3.82/0.98  --sat_epr_types                         true
% 3.82/0.98  --sat_non_cyclic_types                  false
% 3.82/0.98  --sat_finite_models                     false
% 3.82/0.98  --sat_fm_lemmas                         false
% 3.82/0.98  --sat_fm_prep                           false
% 3.82/0.98  --sat_fm_uc_incr                        true
% 3.82/0.98  --sat_out_model                         small
% 3.82/0.98  --sat_out_clauses                       false
% 3.82/0.98  
% 3.82/0.98  ------ QBF Options
% 3.82/0.98  
% 3.82/0.98  --qbf_mode                              false
% 3.82/0.98  --qbf_elim_univ                         false
% 3.82/0.98  --qbf_dom_inst                          none
% 3.82/0.98  --qbf_dom_pre_inst                      false
% 3.82/0.98  --qbf_sk_in                             false
% 3.82/0.98  --qbf_pred_elim                         true
% 3.82/0.98  --qbf_split                             512
% 3.82/0.98  
% 3.82/0.98  ------ BMC1 Options
% 3.82/0.98  
% 3.82/0.98  --bmc1_incremental                      false
% 3.82/0.98  --bmc1_axioms                           reachable_all
% 3.82/0.98  --bmc1_min_bound                        0
% 3.82/0.98  --bmc1_max_bound                        -1
% 3.82/0.98  --bmc1_max_bound_default                -1
% 3.82/0.98  --bmc1_symbol_reachability              true
% 3.82/0.98  --bmc1_property_lemmas                  false
% 3.82/0.98  --bmc1_k_induction                      false
% 3.82/0.98  --bmc1_non_equiv_states                 false
% 3.82/0.98  --bmc1_deadlock                         false
% 3.82/0.98  --bmc1_ucm                              false
% 3.82/0.98  --bmc1_add_unsat_core                   none
% 3.82/0.98  --bmc1_unsat_core_children              false
% 3.82/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.82/0.98  --bmc1_out_stat                         full
% 3.82/0.98  --bmc1_ground_init                      false
% 3.82/0.98  --bmc1_pre_inst_next_state              false
% 3.82/0.98  --bmc1_pre_inst_state                   false
% 3.82/0.98  --bmc1_pre_inst_reach_state             false
% 3.82/0.98  --bmc1_out_unsat_core                   false
% 3.82/0.98  --bmc1_aig_witness_out                  false
% 3.82/0.98  --bmc1_verbose                          false
% 3.82/0.98  --bmc1_dump_clauses_tptp                false
% 3.82/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.82/0.98  --bmc1_dump_file                        -
% 3.82/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.82/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.82/0.98  --bmc1_ucm_extend_mode                  1
% 3.82/0.98  --bmc1_ucm_init_mode                    2
% 3.82/0.98  --bmc1_ucm_cone_mode                    none
% 3.82/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.82/0.98  --bmc1_ucm_relax_model                  4
% 3.82/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.82/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.82/0.98  --bmc1_ucm_layered_model                none
% 3.82/0.98  --bmc1_ucm_max_lemma_size               10
% 3.82/0.98  
% 3.82/0.98  ------ AIG Options
% 3.82/0.98  
% 3.82/0.98  --aig_mode                              false
% 3.82/0.98  
% 3.82/0.98  ------ Instantiation Options
% 3.82/0.98  
% 3.82/0.98  --instantiation_flag                    true
% 3.82/0.98  --inst_sos_flag                         false
% 3.82/0.98  --inst_sos_phase                        true
% 3.82/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.82/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.82/0.98  --inst_lit_sel_side                     num_symb
% 3.82/0.98  --inst_solver_per_active                1400
% 3.82/0.98  --inst_solver_calls_frac                1.
% 3.82/0.98  --inst_passive_queue_type               priority_queues
% 3.82/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.82/0.98  --inst_passive_queues_freq              [25;2]
% 3.82/0.98  --inst_dismatching                      true
% 3.82/0.98  --inst_eager_unprocessed_to_passive     true
% 3.82/0.98  --inst_prop_sim_given                   true
% 3.82/0.98  --inst_prop_sim_new                     false
% 3.82/0.98  --inst_subs_new                         false
% 3.82/0.98  --inst_eq_res_simp                      false
% 3.82/0.98  --inst_subs_given                       false
% 3.82/0.98  --inst_orphan_elimination               true
% 3.82/0.98  --inst_learning_loop_flag               true
% 3.82/0.98  --inst_learning_start                   3000
% 3.82/0.98  --inst_learning_factor                  2
% 3.82/0.98  --inst_start_prop_sim_after_learn       3
% 3.82/0.98  --inst_sel_renew                        solver
% 3.82/0.98  --inst_lit_activity_flag                true
% 3.82/0.98  --inst_restr_to_given                   false
% 3.82/0.98  --inst_activity_threshold               500
% 3.82/0.98  --inst_out_proof                        true
% 3.82/0.98  
% 3.82/0.98  ------ Resolution Options
% 3.82/0.98  
% 3.82/0.98  --resolution_flag                       true
% 3.82/0.98  --res_lit_sel                           adaptive
% 3.82/0.98  --res_lit_sel_side                      none
% 3.82/0.98  --res_ordering                          kbo
% 3.82/0.98  --res_to_prop_solver                    active
% 3.82/0.98  --res_prop_simpl_new                    false
% 3.82/0.98  --res_prop_simpl_given                  true
% 3.82/0.98  --res_passive_queue_type                priority_queues
% 3.82/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.82/0.98  --res_passive_queues_freq               [15;5]
% 3.82/0.98  --res_forward_subs                      full
% 3.82/0.98  --res_backward_subs                     full
% 3.82/0.98  --res_forward_subs_resolution           true
% 3.82/0.98  --res_backward_subs_resolution          true
% 3.82/0.98  --res_orphan_elimination                true
% 3.82/0.98  --res_time_limit                        2.
% 3.82/0.98  --res_out_proof                         true
% 3.82/0.98  
% 3.82/0.98  ------ Superposition Options
% 3.82/0.98  
% 3.82/0.98  --superposition_flag                    true
% 3.82/0.98  --sup_passive_queue_type                priority_queues
% 3.82/0.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.82/0.98  --sup_passive_queues_freq               [1;4]
% 3.82/0.98  --demod_completeness_check              fast
% 3.82/0.98  --demod_use_ground                      true
% 3.82/0.98  --sup_to_prop_solver                    passive
% 3.82/0.98  --sup_prop_simpl_new                    true
% 3.82/0.98  --sup_prop_simpl_given                  true
% 3.82/0.98  --sup_fun_splitting                     false
% 3.82/0.98  --sup_smt_interval                      50000
% 3.82/0.98  
% 3.82/0.98  ------ Superposition Simplification Setup
% 3.82/0.98  
% 3.82/0.98  --sup_indices_passive                   []
% 3.82/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.82/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.82/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.82/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.82/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.82/0.98  --sup_full_bw                           [BwDemod]
% 3.82/0.98  --sup_immed_triv                        [TrivRules]
% 3.82/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.82/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.82/0.98  --sup_immed_bw_main                     []
% 3.82/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.82/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.82/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.82/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.82/0.98  
% 3.82/0.98  ------ Combination Options
% 3.82/0.98  
% 3.82/0.98  --comb_res_mult                         3
% 3.82/0.98  --comb_sup_mult                         2
% 3.82/0.98  --comb_inst_mult                        10
% 3.82/0.98  
% 3.82/0.98  ------ Debug Options
% 3.82/0.98  
% 3.82/0.98  --dbg_backtrace                         false
% 3.82/0.98  --dbg_dump_prop_clauses                 false
% 3.82/0.98  --dbg_dump_prop_clauses_file            -
% 3.82/0.98  --dbg_out_stat                          false
% 3.82/0.98  
% 3.82/0.98  
% 3.82/0.98  
% 3.82/0.98  
% 3.82/0.98  ------ Proving...
% 3.82/0.98  
% 3.82/0.98  
% 3.82/0.98  % SZS status Theorem for theBenchmark.p
% 3.82/0.98  
% 3.82/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.82/0.98  
% 3.82/0.98  fof(f7,conjecture,(
% 3.82/0.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 3.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f8,negated_conjecture,(
% 3.82/0.98    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 3.82/0.98    inference(negated_conjecture,[],[f7])).
% 3.82/0.98  
% 3.82/0.98  fof(f15,plain,(
% 3.82/0.98    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 3.82/0.98    inference(ennf_transformation,[],[f8])).
% 3.82/0.98  
% 3.82/0.98  fof(f16,plain,(
% 3.82/0.98    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.82/0.98    inference(flattening,[],[f15])).
% 3.82/0.98  
% 3.82/0.98  fof(f18,plain,(
% 3.82/0.98    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 3.82/0.98    introduced(choice_axiom,[])).
% 3.82/0.98  
% 3.82/0.98  fof(f19,plain,(
% 3.82/0.98    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 3.82/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).
% 3.82/0.98  
% 3.82/0.98  fof(f28,plain,(
% 3.82/0.98    v1_funct_1(sK2)),
% 3.82/0.98    inference(cnf_transformation,[],[f19])).
% 3.82/0.98  
% 3.82/0.98  fof(f6,axiom,(
% 3.82/0.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)))),
% 3.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f13,plain,(
% 3.82/0.98    ! [X0,X1,X2] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.82/0.98    inference(ennf_transformation,[],[f6])).
% 3.82/0.98  
% 3.82/0.98  fof(f14,plain,(
% 3.82/0.98    ! [X0,X1,X2] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.82/0.98    inference(flattening,[],[f13])).
% 3.82/0.98  
% 3.82/0.98  fof(f26,plain,(
% 3.82/0.98    ( ! [X2,X0,X1] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.82/0.98    inference(cnf_transformation,[],[f14])).
% 3.82/0.98  
% 3.82/0.98  fof(f27,plain,(
% 3.82/0.98    v1_relat_1(sK2)),
% 3.82/0.98    inference(cnf_transformation,[],[f19])).
% 3.82/0.98  
% 3.82/0.98  fof(f29,plain,(
% 3.82/0.98    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 3.82/0.98    inference(cnf_transformation,[],[f19])).
% 3.82/0.98  
% 3.82/0.98  fof(f1,axiom,(
% 3.82/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f17,plain,(
% 3.82/0.98    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.82/0.98    inference(nnf_transformation,[],[f1])).
% 3.82/0.98  
% 3.82/0.98  fof(f21,plain,(
% 3.82/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.82/0.98    inference(cnf_transformation,[],[f17])).
% 3.82/0.98  
% 3.82/0.98  fof(f4,axiom,(
% 3.82/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f24,plain,(
% 3.82/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.82/0.98    inference(cnf_transformation,[],[f4])).
% 3.82/0.98  
% 3.82/0.98  fof(f32,plain,(
% 3.82/0.98    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 3.82/0.98    inference(definition_unfolding,[],[f21,f24])).
% 3.82/0.98  
% 3.82/0.98  fof(f5,axiom,(
% 3.82/0.98    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 3.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f11,plain,(
% 3.82/0.98    ! [X0,X1] : ((k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 3.82/0.98    inference(ennf_transformation,[],[f5])).
% 3.82/0.98  
% 3.82/0.98  fof(f12,plain,(
% 3.82/0.98    ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 3.82/0.98    inference(flattening,[],[f11])).
% 3.82/0.98  
% 3.82/0.98  fof(f25,plain,(
% 3.82/0.98    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 3.82/0.98    inference(cnf_transformation,[],[f12])).
% 3.82/0.98  
% 3.82/0.98  fof(f30,plain,(
% 3.82/0.98    r1_tarski(sK0,k2_relat_1(sK2))),
% 3.82/0.98    inference(cnf_transformation,[],[f19])).
% 3.82/0.98  
% 3.82/0.98  fof(f3,axiom,(
% 3.82/0.98    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f23,plain,(
% 3.82/0.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.82/0.98    inference(cnf_transformation,[],[f3])).
% 3.82/0.98  
% 3.82/0.98  fof(f34,plain,(
% 3.82/0.98    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 3.82/0.98    inference(definition_unfolding,[],[f23,f24])).
% 3.82/0.98  
% 3.82/0.98  fof(f2,axiom,(
% 3.82/0.98    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.82/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f9,plain,(
% 3.82/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.82/0.98    inference(ennf_transformation,[],[f2])).
% 3.82/0.98  
% 3.82/0.98  fof(f10,plain,(
% 3.82/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.82/0.98    inference(flattening,[],[f9])).
% 3.82/0.98  
% 3.82/0.98  fof(f22,plain,(
% 3.82/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.82/0.98    inference(cnf_transformation,[],[f10])).
% 3.82/0.98  
% 3.82/0.98  fof(f20,plain,(
% 3.82/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.82/0.98    inference(cnf_transformation,[],[f17])).
% 3.82/0.98  
% 3.82/0.98  fof(f33,plain,(
% 3.82/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 3.82/0.98    inference(definition_unfolding,[],[f20,f24])).
% 3.82/0.98  
% 3.82/0.98  fof(f31,plain,(
% 3.82/0.98    ~r1_tarski(sK0,sK1)),
% 3.82/0.98    inference(cnf_transformation,[],[f19])).
% 3.82/0.98  
% 3.82/0.98  cnf(c_9,negated_conjecture,
% 3.82/0.98      ( v1_funct_1(sK2) ),
% 3.82/0.98      inference(cnf_transformation,[],[f28]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_403,plain,
% 3.82/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_5,plain,
% 3.82/0.98      ( ~ v1_funct_1(X0)
% 3.82/0.98      | ~ v1_relat_1(X0)
% 3.82/0.98      | k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2)) ),
% 3.82/0.98      inference(cnf_transformation,[],[f26]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_407,plain,
% 3.82/0.98      ( k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2))
% 3.82/0.98      | v1_funct_1(X0) != iProver_top
% 3.82/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_986,plain,
% 3.82/0.98      ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1))
% 3.82/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_403,c_407]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_10,negated_conjecture,
% 3.82/0.98      ( v1_relat_1(sK2) ),
% 3.82/0.98      inference(cnf_transformation,[],[f27]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_11,plain,
% 3.82/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_2357,plain,
% 3.82/0.98      ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1)) ),
% 3.82/0.98      inference(global_propositional_subsumption,
% 3.82/0.98                [status(thm)],
% 3.82/0.98                [c_986,c_11]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_8,negated_conjecture,
% 3.82/0.98      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
% 3.82/0.98      inference(cnf_transformation,[],[f29]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_404,plain,
% 3.82/0.98      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_0,plain,
% 3.82/0.98      ( ~ r1_tarski(X0,X1) | k6_subset_1(X0,X1) = k1_xboole_0 ),
% 3.82/0.98      inference(cnf_transformation,[],[f32]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_412,plain,
% 3.82/0.98      ( k6_subset_1(X0,X1) = k1_xboole_0
% 3.82/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_777,plain,
% 3.82/0.98      ( k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k1_xboole_0 ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_404,c_412]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_2367,plain,
% 3.82/0.98      ( k10_relat_1(sK2,k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_2357,c_777]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_4,plain,
% 3.82/0.98      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 3.82/0.98      | ~ v1_relat_1(X1)
% 3.82/0.98      | k10_relat_1(X1,X0) != k1_xboole_0
% 3.82/0.98      | k1_xboole_0 = X0 ),
% 3.82/0.98      inference(cnf_transformation,[],[f25]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_408,plain,
% 3.82/0.98      ( k10_relat_1(X0,X1) != k1_xboole_0
% 3.82/0.98      | k1_xboole_0 = X1
% 3.82/0.98      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 3.82/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_5206,plain,
% 3.82/0.98      ( k6_subset_1(sK0,sK1) = k1_xboole_0
% 3.82/0.98      | r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2)) != iProver_top
% 3.82/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_2367,c_408]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_5518,plain,
% 3.82/0.98      ( r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2)) != iProver_top
% 3.82/0.98      | k6_subset_1(sK0,sK1) = k1_xboole_0 ),
% 3.82/0.98      inference(global_propositional_subsumption,
% 3.82/0.98                [status(thm)],
% 3.82/0.98                [c_5206,c_11]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_5519,plain,
% 3.82/0.98      ( k6_subset_1(sK0,sK1) = k1_xboole_0
% 3.82/0.98      | r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2)) != iProver_top ),
% 3.82/0.98      inference(renaming,[status(thm)],[c_5518]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_7,negated_conjecture,
% 3.82/0.98      ( r1_tarski(sK0,k2_relat_1(sK2)) ),
% 3.82/0.98      inference(cnf_transformation,[],[f30]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_405,plain,
% 3.82/0.98      ( r1_tarski(sK0,k2_relat_1(sK2)) = iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_3,plain,
% 3.82/0.98      ( r1_tarski(k6_subset_1(X0,X1),X0) ),
% 3.82/0.98      inference(cnf_transformation,[],[f34]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_409,plain,
% 3.82/0.98      ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_2,plain,
% 3.82/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.82/0.98      inference(cnf_transformation,[],[f22]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_410,plain,
% 3.82/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.82/0.98      | r1_tarski(X1,X2) != iProver_top
% 3.82/0.98      | r1_tarski(X0,X2) = iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_859,plain,
% 3.82/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.82/0.98      | r1_tarski(k6_subset_1(X0,X2),X1) = iProver_top ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_409,c_410]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_1650,plain,
% 3.82/0.98      ( k6_subset_1(k6_subset_1(X0,X1),X2) = k1_xboole_0
% 3.82/0.98      | r1_tarski(X0,X2) != iProver_top ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_859,c_412]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_2627,plain,
% 3.82/0.98      ( k6_subset_1(k6_subset_1(sK0,X0),k2_relat_1(sK2)) = k1_xboole_0 ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_405,c_1650]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_1,plain,
% 3.82/0.98      ( r1_tarski(X0,X1) | k6_subset_1(X0,X1) != k1_xboole_0 ),
% 3.82/0.98      inference(cnf_transformation,[],[f33]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_411,plain,
% 3.82/0.98      ( k6_subset_1(X0,X1) != k1_xboole_0
% 3.82/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_3022,plain,
% 3.82/0.98      ( r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2)) = iProver_top ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_2627,c_411]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_5524,plain,
% 3.82/0.98      ( k6_subset_1(sK0,sK1) = k1_xboole_0 ),
% 3.82/0.98      inference(forward_subsumption_resolution,
% 3.82/0.98                [status(thm)],
% 3.82/0.98                [c_5519,c_3022]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_5533,plain,
% 3.82/0.98      ( r1_tarski(sK0,sK1) = iProver_top ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_5524,c_411]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_6,negated_conjecture,
% 3.82/0.98      ( ~ r1_tarski(sK0,sK1) ),
% 3.82/0.98      inference(cnf_transformation,[],[f31]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_15,plain,
% 3.82/0.98      ( r1_tarski(sK0,sK1) != iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(contradiction,plain,
% 3.82/0.98      ( $false ),
% 3.82/0.98      inference(minisat,[status(thm)],[c_5533,c_15]) ).
% 3.82/0.98  
% 3.82/0.98  
% 3.82/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.82/0.98  
% 3.82/0.98  ------                               Statistics
% 3.82/0.98  
% 3.82/0.98  ------ Selected
% 3.82/0.98  
% 3.82/0.98  total_time:                             0.211
% 3.82/0.98  
%------------------------------------------------------------------------------
