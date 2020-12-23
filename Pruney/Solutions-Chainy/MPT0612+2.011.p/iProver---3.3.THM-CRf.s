%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:48:58 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   68 (  96 expanded)
%              Number of clauses        :   30 (  32 expanded)
%              Number of leaves         :   10 (  18 expanded)
%              Depth                    :   13
%              Number of atoms          :  156 ( 244 expanded)
%              Number of equality atoms :   59 (  87 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) = k1_xboole_0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) != k1_xboole_0
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) != k1_xboole_0
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) != k1_xboole_0
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) != k1_xboole_0
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) != k1_xboole_0
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f24])).

fof(f37,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k6_subset_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_393,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_132,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_5,c_9])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_151,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | k7_relat_1(X0,X1) = X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_132,c_12])).

cnf(c_152,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),X0)
    | k7_relat_1(sK2,X0) = sK2 ),
    inference(unflattening,[status(thm)],[c_151])).

cnf(c_390,plain,
    ( k7_relat_1(sK2,X0) = sK2
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_152])).

cnf(c_570,plain,
    ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_393,c_390])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k6_subset_1(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_163,plain,
    ( k6_subset_1(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k6_subset_1(X1,X2))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_12])).

cnf(c_164,plain,
    ( k6_subset_1(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1)) = k7_relat_1(sK2,k6_subset_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_163])).

cnf(c_617,plain,
    ( k7_relat_1(sK2,k6_subset_1(k1_relat_1(sK2),X0)) = k6_subset_1(sK2,k7_relat_1(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_570,c_164])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_391,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_xboole_0(X0,k6_subset_1(X2,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_392,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X0,k6_subset_1(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_395,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_734,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(k6_subset_1(X2,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_392,c_395])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_169,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_12])).

cnf(c_170,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k7_relat_1(k7_relat_1(sK2,X0),X1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_169])).

cnf(c_389,plain,
    ( k7_relat_1(k7_relat_1(sK2,X0),X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_170])).

cnf(c_937,plain,
    ( k7_relat_1(k7_relat_1(sK2,k6_subset_1(X0,X1)),X2) = k1_xboole_0
    | r1_tarski(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_734,c_389])).

cnf(c_2621,plain,
    ( k7_relat_1(k7_relat_1(sK2,k6_subset_1(X0,sK1)),sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_391,c_937])).

cnf(c_2765,plain,
    ( k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_617,c_2621])).

cnf(c_10,negated_conjecture,
    ( k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2765,c_10])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:34:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.89/0.94  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/0.94  
% 1.89/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.89/0.94  
% 1.89/0.94  ------  iProver source info
% 1.89/0.94  
% 1.89/0.94  git: date: 2020-06-30 10:37:57 +0100
% 1.89/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.89/0.94  git: non_committed_changes: false
% 1.89/0.94  git: last_make_outside_of_git: false
% 1.89/0.94  
% 1.89/0.94  ------ 
% 1.89/0.94  
% 1.89/0.94  ------ Input Options
% 1.89/0.94  
% 1.89/0.94  --out_options                           all
% 1.89/0.94  --tptp_safe_out                         true
% 1.89/0.94  --problem_path                          ""
% 1.89/0.94  --include_path                          ""
% 1.89/0.94  --clausifier                            res/vclausify_rel
% 1.89/0.94  --clausifier_options                    --mode clausify
% 1.89/0.94  --stdin                                 false
% 1.89/0.94  --stats_out                             all
% 1.89/0.94  
% 1.89/0.94  ------ General Options
% 1.89/0.94  
% 1.89/0.94  --fof                                   false
% 1.89/0.94  --time_out_real                         305.
% 1.89/0.94  --time_out_virtual                      -1.
% 1.89/0.94  --symbol_type_check                     false
% 1.89/0.94  --clausify_out                          false
% 1.89/0.94  --sig_cnt_out                           false
% 1.89/0.94  --trig_cnt_out                          false
% 1.89/0.94  --trig_cnt_out_tolerance                1.
% 1.89/0.94  --trig_cnt_out_sk_spl                   false
% 1.89/0.94  --abstr_cl_out                          false
% 1.89/0.94  
% 1.89/0.94  ------ Global Options
% 1.89/0.94  
% 1.89/0.94  --schedule                              default
% 1.89/0.94  --add_important_lit                     false
% 1.89/0.94  --prop_solver_per_cl                    1000
% 1.89/0.94  --min_unsat_core                        false
% 1.89/0.94  --soft_assumptions                      false
% 1.89/0.94  --soft_lemma_size                       3
% 1.89/0.94  --prop_impl_unit_size                   0
% 1.89/0.94  --prop_impl_unit                        []
% 1.89/0.94  --share_sel_clauses                     true
% 1.89/0.94  --reset_solvers                         false
% 1.89/0.94  --bc_imp_inh                            [conj_cone]
% 1.89/0.94  --conj_cone_tolerance                   3.
% 1.89/0.94  --extra_neg_conj                        none
% 1.89/0.94  --large_theory_mode                     true
% 1.89/0.94  --prolific_symb_bound                   200
% 1.89/0.94  --lt_threshold                          2000
% 1.89/0.94  --clause_weak_htbl                      true
% 1.89/0.94  --gc_record_bc_elim                     false
% 1.89/0.94  
% 1.89/0.94  ------ Preprocessing Options
% 1.89/0.94  
% 1.89/0.94  --preprocessing_flag                    true
% 1.89/0.94  --time_out_prep_mult                    0.1
% 1.89/0.94  --splitting_mode                        input
% 1.89/0.94  --splitting_grd                         true
% 1.89/0.94  --splitting_cvd                         false
% 1.89/0.94  --splitting_cvd_svl                     false
% 1.89/0.94  --splitting_nvd                         32
% 1.89/0.94  --sub_typing                            true
% 1.89/0.94  --prep_gs_sim                           true
% 1.89/0.94  --prep_unflatten                        true
% 1.89/0.94  --prep_res_sim                          true
% 1.89/0.94  --prep_upred                            true
% 1.89/0.94  --prep_sem_filter                       exhaustive
% 1.89/0.94  --prep_sem_filter_out                   false
% 1.89/0.94  --pred_elim                             true
% 1.89/0.94  --res_sim_input                         true
% 1.89/0.94  --eq_ax_congr_red                       true
% 1.89/0.94  --pure_diseq_elim                       true
% 1.89/0.94  --brand_transform                       false
% 1.89/0.94  --non_eq_to_eq                          false
% 1.89/0.94  --prep_def_merge                        true
% 1.89/0.94  --prep_def_merge_prop_impl              false
% 1.89/0.94  --prep_def_merge_mbd                    true
% 1.89/0.94  --prep_def_merge_tr_red                 false
% 1.89/0.94  --prep_def_merge_tr_cl                  false
% 1.89/0.94  --smt_preprocessing                     true
% 1.89/0.94  --smt_ac_axioms                         fast
% 1.89/0.94  --preprocessed_out                      false
% 1.89/0.94  --preprocessed_stats                    false
% 1.89/0.94  
% 1.89/0.94  ------ Abstraction refinement Options
% 1.89/0.94  
% 1.89/0.94  --abstr_ref                             []
% 1.89/0.94  --abstr_ref_prep                        false
% 1.89/0.94  --abstr_ref_until_sat                   false
% 1.89/0.94  --abstr_ref_sig_restrict                funpre
% 1.89/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 1.89/0.94  --abstr_ref_under                       []
% 1.89/0.94  
% 1.89/0.94  ------ SAT Options
% 1.89/0.94  
% 1.89/0.94  --sat_mode                              false
% 1.89/0.94  --sat_fm_restart_options                ""
% 1.89/0.94  --sat_gr_def                            false
% 1.89/0.94  --sat_epr_types                         true
% 1.89/0.94  --sat_non_cyclic_types                  false
% 1.89/0.94  --sat_finite_models                     false
% 1.89/0.94  --sat_fm_lemmas                         false
% 1.89/0.94  --sat_fm_prep                           false
% 1.89/0.94  --sat_fm_uc_incr                        true
% 1.89/0.94  --sat_out_model                         small
% 1.89/0.94  --sat_out_clauses                       false
% 1.89/0.94  
% 1.89/0.94  ------ QBF Options
% 1.89/0.94  
% 1.89/0.94  --qbf_mode                              false
% 1.89/0.94  --qbf_elim_univ                         false
% 1.89/0.94  --qbf_dom_inst                          none
% 1.89/0.94  --qbf_dom_pre_inst                      false
% 1.89/0.94  --qbf_sk_in                             false
% 1.89/0.94  --qbf_pred_elim                         true
% 1.89/0.94  --qbf_split                             512
% 1.89/0.94  
% 1.89/0.94  ------ BMC1 Options
% 1.89/0.94  
% 1.89/0.94  --bmc1_incremental                      false
% 1.89/0.94  --bmc1_axioms                           reachable_all
% 1.89/0.94  --bmc1_min_bound                        0
% 1.89/0.94  --bmc1_max_bound                        -1
% 1.89/0.94  --bmc1_max_bound_default                -1
% 1.89/0.94  --bmc1_symbol_reachability              true
% 1.89/0.94  --bmc1_property_lemmas                  false
% 1.89/0.94  --bmc1_k_induction                      false
% 1.89/0.94  --bmc1_non_equiv_states                 false
% 1.89/0.94  --bmc1_deadlock                         false
% 1.89/0.94  --bmc1_ucm                              false
% 1.89/0.94  --bmc1_add_unsat_core                   none
% 1.89/0.94  --bmc1_unsat_core_children              false
% 1.89/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 1.89/0.94  --bmc1_out_stat                         full
% 1.89/0.94  --bmc1_ground_init                      false
% 1.89/0.94  --bmc1_pre_inst_next_state              false
% 1.89/0.94  --bmc1_pre_inst_state                   false
% 1.89/0.94  --bmc1_pre_inst_reach_state             false
% 1.89/0.94  --bmc1_out_unsat_core                   false
% 1.89/0.94  --bmc1_aig_witness_out                  false
% 1.89/0.94  --bmc1_verbose                          false
% 1.89/0.94  --bmc1_dump_clauses_tptp                false
% 1.89/0.94  --bmc1_dump_unsat_core_tptp             false
% 1.89/0.94  --bmc1_dump_file                        -
% 1.89/0.94  --bmc1_ucm_expand_uc_limit              128
% 1.89/0.94  --bmc1_ucm_n_expand_iterations          6
% 1.89/0.94  --bmc1_ucm_extend_mode                  1
% 1.89/0.94  --bmc1_ucm_init_mode                    2
% 1.89/0.94  --bmc1_ucm_cone_mode                    none
% 1.89/0.94  --bmc1_ucm_reduced_relation_type        0
% 1.89/0.94  --bmc1_ucm_relax_model                  4
% 1.89/0.94  --bmc1_ucm_full_tr_after_sat            true
% 1.89/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 1.89/0.94  --bmc1_ucm_layered_model                none
% 1.89/0.94  --bmc1_ucm_max_lemma_size               10
% 1.89/0.94  
% 1.89/0.94  ------ AIG Options
% 1.89/0.94  
% 1.89/0.94  --aig_mode                              false
% 1.89/0.94  
% 1.89/0.94  ------ Instantiation Options
% 1.89/0.94  
% 1.89/0.94  --instantiation_flag                    true
% 1.89/0.94  --inst_sos_flag                         false
% 1.89/0.94  --inst_sos_phase                        true
% 1.89/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.89/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.89/0.94  --inst_lit_sel_side                     num_symb
% 1.89/0.94  --inst_solver_per_active                1400
% 1.89/0.94  --inst_solver_calls_frac                1.
% 1.89/0.94  --inst_passive_queue_type               priority_queues
% 1.89/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.89/0.94  --inst_passive_queues_freq              [25;2]
% 1.89/0.94  --inst_dismatching                      true
% 1.89/0.94  --inst_eager_unprocessed_to_passive     true
% 1.89/0.94  --inst_prop_sim_given                   true
% 1.89/0.94  --inst_prop_sim_new                     false
% 1.89/0.94  --inst_subs_new                         false
% 1.89/0.94  --inst_eq_res_simp                      false
% 1.89/0.94  --inst_subs_given                       false
% 1.89/0.94  --inst_orphan_elimination               true
% 1.89/0.94  --inst_learning_loop_flag               true
% 1.89/0.94  --inst_learning_start                   3000
% 1.89/0.94  --inst_learning_factor                  2
% 1.89/0.94  --inst_start_prop_sim_after_learn       3
% 1.89/0.94  --inst_sel_renew                        solver
% 1.89/0.94  --inst_lit_activity_flag                true
% 1.89/0.94  --inst_restr_to_given                   false
% 1.89/0.94  --inst_activity_threshold               500
% 1.89/0.94  --inst_out_proof                        true
% 1.89/0.94  
% 1.89/0.94  ------ Resolution Options
% 1.89/0.94  
% 1.89/0.94  --resolution_flag                       true
% 1.89/0.94  --res_lit_sel                           adaptive
% 1.89/0.94  --res_lit_sel_side                      none
% 1.89/0.94  --res_ordering                          kbo
% 1.89/0.94  --res_to_prop_solver                    active
% 1.89/0.94  --res_prop_simpl_new                    false
% 1.89/0.94  --res_prop_simpl_given                  true
% 1.89/0.94  --res_passive_queue_type                priority_queues
% 1.89/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.89/0.94  --res_passive_queues_freq               [15;5]
% 1.89/0.94  --res_forward_subs                      full
% 1.89/0.94  --res_backward_subs                     full
% 1.89/0.94  --res_forward_subs_resolution           true
% 1.89/0.94  --res_backward_subs_resolution          true
% 1.89/0.94  --res_orphan_elimination                true
% 1.89/0.94  --res_time_limit                        2.
% 1.89/0.94  --res_out_proof                         true
% 1.89/0.94  
% 1.89/0.94  ------ Superposition Options
% 1.89/0.94  
% 1.89/0.94  --superposition_flag                    true
% 1.89/0.94  --sup_passive_queue_type                priority_queues
% 1.89/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.89/0.94  --sup_passive_queues_freq               [8;1;4]
% 1.89/0.94  --demod_completeness_check              fast
% 1.89/0.94  --demod_use_ground                      true
% 1.89/0.94  --sup_to_prop_solver                    passive
% 1.89/0.94  --sup_prop_simpl_new                    true
% 1.89/0.94  --sup_prop_simpl_given                  true
% 1.89/0.94  --sup_fun_splitting                     false
% 1.89/0.94  --sup_smt_interval                      50000
% 1.89/0.94  
% 1.89/0.94  ------ Superposition Simplification Setup
% 1.89/0.94  
% 1.89/0.94  --sup_indices_passive                   []
% 1.89/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 1.89/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/0.94  --sup_full_bw                           [BwDemod]
% 1.89/0.94  --sup_immed_triv                        [TrivRules]
% 1.89/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.89/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/0.94  --sup_immed_bw_main                     []
% 1.89/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.89/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 1.89/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.89/0.94  
% 1.89/0.94  ------ Combination Options
% 1.89/0.94  
% 1.89/0.94  --comb_res_mult                         3
% 1.89/0.94  --comb_sup_mult                         2
% 1.89/0.94  --comb_inst_mult                        10
% 1.89/0.94  
% 1.89/0.94  ------ Debug Options
% 1.89/0.94  
% 1.89/0.94  --dbg_backtrace                         false
% 1.89/0.94  --dbg_dump_prop_clauses                 false
% 1.89/0.94  --dbg_dump_prop_clauses_file            -
% 1.89/0.94  --dbg_out_stat                          false
% 1.89/0.94  ------ Parsing...
% 1.89/0.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.89/0.94  
% 1.89/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.89/0.94  
% 1.89/0.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.89/0.94  
% 1.89/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.89/0.94  ------ Proving...
% 1.89/0.94  ------ Problem Properties 
% 1.89/0.94  
% 1.89/0.94  
% 1.89/0.94  clauses                                 9
% 1.89/0.94  conjectures                             2
% 1.89/0.94  EPR                                     4
% 1.89/0.94  Horn                                    9
% 1.89/0.94  unary                                   4
% 1.89/0.94  binary                                  4
% 1.89/0.94  lits                                    15
% 1.89/0.94  lits eq                                 5
% 1.89/0.94  fd_pure                                 0
% 1.89/0.94  fd_pseudo                               0
% 1.89/0.94  fd_cond                                 0
% 1.89/0.94  fd_pseudo_cond                          1
% 1.89/0.94  AC symbols                              0
% 1.89/0.94  
% 1.89/0.94  ------ Schedule dynamic 5 is on 
% 1.89/0.94  
% 1.89/0.94  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.89/0.94  
% 1.89/0.94  
% 1.89/0.94  ------ 
% 1.89/0.94  Current options:
% 1.89/0.94  ------ 
% 1.89/0.94  
% 1.89/0.94  ------ Input Options
% 1.89/0.94  
% 1.89/0.94  --out_options                           all
% 1.89/0.94  --tptp_safe_out                         true
% 1.89/0.94  --problem_path                          ""
% 1.89/0.94  --include_path                          ""
% 1.89/0.94  --clausifier                            res/vclausify_rel
% 1.89/0.94  --clausifier_options                    --mode clausify
% 1.89/0.94  --stdin                                 false
% 1.89/0.94  --stats_out                             all
% 1.89/0.94  
% 1.89/0.94  ------ General Options
% 1.89/0.94  
% 1.89/0.94  --fof                                   false
% 1.89/0.94  --time_out_real                         305.
% 1.89/0.94  --time_out_virtual                      -1.
% 1.89/0.94  --symbol_type_check                     false
% 1.89/0.94  --clausify_out                          false
% 1.89/0.94  --sig_cnt_out                           false
% 1.89/0.94  --trig_cnt_out                          false
% 1.89/0.94  --trig_cnt_out_tolerance                1.
% 1.89/0.94  --trig_cnt_out_sk_spl                   false
% 1.89/0.94  --abstr_cl_out                          false
% 1.89/0.94  
% 1.89/0.94  ------ Global Options
% 1.89/0.94  
% 1.89/0.94  --schedule                              default
% 1.89/0.94  --add_important_lit                     false
% 1.89/0.94  --prop_solver_per_cl                    1000
% 1.89/0.94  --min_unsat_core                        false
% 1.89/0.94  --soft_assumptions                      false
% 1.89/0.94  --soft_lemma_size                       3
% 1.89/0.94  --prop_impl_unit_size                   0
% 1.89/0.94  --prop_impl_unit                        []
% 1.89/0.94  --share_sel_clauses                     true
% 1.89/0.94  --reset_solvers                         false
% 1.89/0.94  --bc_imp_inh                            [conj_cone]
% 1.89/0.94  --conj_cone_tolerance                   3.
% 1.89/0.94  --extra_neg_conj                        none
% 1.89/0.94  --large_theory_mode                     true
% 1.89/0.94  --prolific_symb_bound                   200
% 1.89/0.94  --lt_threshold                          2000
% 1.89/0.94  --clause_weak_htbl                      true
% 1.89/0.94  --gc_record_bc_elim                     false
% 1.89/0.94  
% 1.89/0.94  ------ Preprocessing Options
% 1.89/0.94  
% 1.89/0.94  --preprocessing_flag                    true
% 1.89/0.94  --time_out_prep_mult                    0.1
% 1.89/0.94  --splitting_mode                        input
% 1.89/0.94  --splitting_grd                         true
% 1.89/0.94  --splitting_cvd                         false
% 1.89/0.94  --splitting_cvd_svl                     false
% 1.89/0.94  --splitting_nvd                         32
% 1.89/0.94  --sub_typing                            true
% 1.89/0.94  --prep_gs_sim                           true
% 1.89/0.94  --prep_unflatten                        true
% 1.89/0.94  --prep_res_sim                          true
% 1.89/0.94  --prep_upred                            true
% 1.89/0.94  --prep_sem_filter                       exhaustive
% 1.89/0.94  --prep_sem_filter_out                   false
% 1.89/0.94  --pred_elim                             true
% 1.89/0.94  --res_sim_input                         true
% 1.89/0.94  --eq_ax_congr_red                       true
% 1.89/0.94  --pure_diseq_elim                       true
% 1.89/0.94  --brand_transform                       false
% 1.89/0.94  --non_eq_to_eq                          false
% 1.89/0.94  --prep_def_merge                        true
% 1.89/0.94  --prep_def_merge_prop_impl              false
% 1.89/0.94  --prep_def_merge_mbd                    true
% 1.89/0.94  --prep_def_merge_tr_red                 false
% 1.89/0.94  --prep_def_merge_tr_cl                  false
% 1.89/0.94  --smt_preprocessing                     true
% 1.89/0.94  --smt_ac_axioms                         fast
% 1.89/0.94  --preprocessed_out                      false
% 1.89/0.94  --preprocessed_stats                    false
% 1.89/0.94  
% 1.89/0.94  ------ Abstraction refinement Options
% 1.89/0.94  
% 1.89/0.94  --abstr_ref                             []
% 1.89/0.94  --abstr_ref_prep                        false
% 1.89/0.94  --abstr_ref_until_sat                   false
% 1.89/0.94  --abstr_ref_sig_restrict                funpre
% 1.89/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 1.89/0.94  --abstr_ref_under                       []
% 1.89/0.94  
% 1.89/0.94  ------ SAT Options
% 1.89/0.94  
% 1.89/0.94  --sat_mode                              false
% 1.89/0.94  --sat_fm_restart_options                ""
% 1.89/0.94  --sat_gr_def                            false
% 1.89/0.94  --sat_epr_types                         true
% 1.89/0.94  --sat_non_cyclic_types                  false
% 1.89/0.94  --sat_finite_models                     false
% 1.89/0.94  --sat_fm_lemmas                         false
% 1.89/0.94  --sat_fm_prep                           false
% 1.89/0.94  --sat_fm_uc_incr                        true
% 1.89/0.94  --sat_out_model                         small
% 1.89/0.94  --sat_out_clauses                       false
% 1.89/0.94  
% 1.89/0.94  ------ QBF Options
% 1.89/0.94  
% 1.89/0.94  --qbf_mode                              false
% 1.89/0.94  --qbf_elim_univ                         false
% 1.89/0.94  --qbf_dom_inst                          none
% 1.89/0.94  --qbf_dom_pre_inst                      false
% 1.89/0.94  --qbf_sk_in                             false
% 1.89/0.94  --qbf_pred_elim                         true
% 1.89/0.94  --qbf_split                             512
% 1.89/0.94  
% 1.89/0.94  ------ BMC1 Options
% 1.89/0.94  
% 1.89/0.94  --bmc1_incremental                      false
% 1.89/0.94  --bmc1_axioms                           reachable_all
% 1.89/0.94  --bmc1_min_bound                        0
% 1.89/0.94  --bmc1_max_bound                        -1
% 1.89/0.94  --bmc1_max_bound_default                -1
% 1.89/0.94  --bmc1_symbol_reachability              true
% 1.89/0.94  --bmc1_property_lemmas                  false
% 1.89/0.94  --bmc1_k_induction                      false
% 1.89/0.94  --bmc1_non_equiv_states                 false
% 1.89/0.94  --bmc1_deadlock                         false
% 1.89/0.94  --bmc1_ucm                              false
% 1.89/0.94  --bmc1_add_unsat_core                   none
% 1.89/0.94  --bmc1_unsat_core_children              false
% 1.89/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 1.89/0.94  --bmc1_out_stat                         full
% 1.89/0.94  --bmc1_ground_init                      false
% 1.89/0.94  --bmc1_pre_inst_next_state              false
% 1.89/0.94  --bmc1_pre_inst_state                   false
% 1.89/0.94  --bmc1_pre_inst_reach_state             false
% 1.89/0.94  --bmc1_out_unsat_core                   false
% 1.89/0.94  --bmc1_aig_witness_out                  false
% 1.89/0.94  --bmc1_verbose                          false
% 1.89/0.94  --bmc1_dump_clauses_tptp                false
% 1.89/0.94  --bmc1_dump_unsat_core_tptp             false
% 1.89/0.94  --bmc1_dump_file                        -
% 1.89/0.94  --bmc1_ucm_expand_uc_limit              128
% 1.89/0.94  --bmc1_ucm_n_expand_iterations          6
% 1.89/0.94  --bmc1_ucm_extend_mode                  1
% 1.89/0.94  --bmc1_ucm_init_mode                    2
% 1.89/0.94  --bmc1_ucm_cone_mode                    none
% 1.89/0.94  --bmc1_ucm_reduced_relation_type        0
% 1.89/0.94  --bmc1_ucm_relax_model                  4
% 1.89/0.94  --bmc1_ucm_full_tr_after_sat            true
% 1.89/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 1.89/0.94  --bmc1_ucm_layered_model                none
% 1.89/0.94  --bmc1_ucm_max_lemma_size               10
% 1.89/0.94  
% 1.89/0.94  ------ AIG Options
% 1.89/0.94  
% 1.89/0.94  --aig_mode                              false
% 1.89/0.94  
% 1.89/0.94  ------ Instantiation Options
% 1.89/0.94  
% 1.89/0.94  --instantiation_flag                    true
% 1.89/0.94  --inst_sos_flag                         false
% 1.89/0.94  --inst_sos_phase                        true
% 1.89/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.89/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.89/0.94  --inst_lit_sel_side                     none
% 1.89/0.94  --inst_solver_per_active                1400
% 1.89/0.94  --inst_solver_calls_frac                1.
% 1.89/0.94  --inst_passive_queue_type               priority_queues
% 1.89/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.89/0.94  --inst_passive_queues_freq              [25;2]
% 1.89/0.94  --inst_dismatching                      true
% 1.89/0.94  --inst_eager_unprocessed_to_passive     true
% 1.89/0.94  --inst_prop_sim_given                   true
% 1.89/0.94  --inst_prop_sim_new                     false
% 1.89/0.94  --inst_subs_new                         false
% 1.89/0.94  --inst_eq_res_simp                      false
% 1.89/0.94  --inst_subs_given                       false
% 1.89/0.94  --inst_orphan_elimination               true
% 1.89/0.94  --inst_learning_loop_flag               true
% 1.89/0.94  --inst_learning_start                   3000
% 1.89/0.94  --inst_learning_factor                  2
% 1.89/0.94  --inst_start_prop_sim_after_learn       3
% 1.89/0.94  --inst_sel_renew                        solver
% 1.89/0.94  --inst_lit_activity_flag                true
% 1.89/0.94  --inst_restr_to_given                   false
% 1.89/0.94  --inst_activity_threshold               500
% 1.89/0.94  --inst_out_proof                        true
% 1.89/0.94  
% 1.89/0.94  ------ Resolution Options
% 1.89/0.94  
% 1.89/0.94  --resolution_flag                       false
% 1.89/0.94  --res_lit_sel                           adaptive
% 1.89/0.94  --res_lit_sel_side                      none
% 1.89/0.94  --res_ordering                          kbo
% 1.89/0.94  --res_to_prop_solver                    active
% 1.89/0.94  --res_prop_simpl_new                    false
% 1.89/0.94  --res_prop_simpl_given                  true
% 1.89/0.94  --res_passive_queue_type                priority_queues
% 1.89/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.89/0.94  --res_passive_queues_freq               [15;5]
% 1.89/0.94  --res_forward_subs                      full
% 1.89/0.94  --res_backward_subs                     full
% 1.89/0.94  --res_forward_subs_resolution           true
% 1.89/0.94  --res_backward_subs_resolution          true
% 1.89/0.94  --res_orphan_elimination                true
% 1.89/0.94  --res_time_limit                        2.
% 1.89/0.94  --res_out_proof                         true
% 1.89/0.94  
% 1.89/0.94  ------ Superposition Options
% 1.89/0.94  
% 1.89/0.94  --superposition_flag                    true
% 1.89/0.94  --sup_passive_queue_type                priority_queues
% 1.89/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.89/0.94  --sup_passive_queues_freq               [8;1;4]
% 1.89/0.94  --demod_completeness_check              fast
% 1.89/0.94  --demod_use_ground                      true
% 1.89/0.94  --sup_to_prop_solver                    passive
% 1.89/0.94  --sup_prop_simpl_new                    true
% 1.89/0.94  --sup_prop_simpl_given                  true
% 1.89/0.94  --sup_fun_splitting                     false
% 1.89/0.94  --sup_smt_interval                      50000
% 1.89/0.94  
% 1.89/0.94  ------ Superposition Simplification Setup
% 1.89/0.94  
% 1.89/0.94  --sup_indices_passive                   []
% 1.89/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.89/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 1.89/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/0.94  --sup_full_bw                           [BwDemod]
% 1.89/0.94  --sup_immed_triv                        [TrivRules]
% 1.89/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.89/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/0.94  --sup_immed_bw_main                     []
% 1.89/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.89/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 1.89/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.89/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.89/0.94  
% 1.89/0.94  ------ Combination Options
% 1.89/0.94  
% 1.89/0.94  --comb_res_mult                         3
% 1.89/0.94  --comb_sup_mult                         2
% 1.89/0.94  --comb_inst_mult                        10
% 1.89/0.94  
% 1.89/0.94  ------ Debug Options
% 1.89/0.94  
% 1.89/0.94  --dbg_backtrace                         false
% 1.89/0.94  --dbg_dump_prop_clauses                 false
% 1.89/0.94  --dbg_dump_prop_clauses_file            -
% 1.89/0.94  --dbg_out_stat                          false
% 1.89/0.94  
% 1.89/0.94  
% 1.89/0.94  
% 1.89/0.94  
% 1.89/0.94  ------ Proving...
% 1.89/0.94  
% 1.89/0.94  
% 1.89/0.94  % SZS status Theorem for theBenchmark.p
% 1.89/0.94  
% 1.89/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 1.89/0.94  
% 1.89/0.94  fof(f2,axiom,(
% 1.89/0.94    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.89/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.94  
% 1.89/0.94  fof(f21,plain,(
% 1.89/0.94    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.89/0.94    inference(nnf_transformation,[],[f2])).
% 1.89/0.94  
% 1.89/0.94  fof(f22,plain,(
% 1.89/0.94    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.89/0.94    inference(flattening,[],[f21])).
% 1.89/0.94  
% 1.89/0.94  fof(f27,plain,(
% 1.89/0.94    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.89/0.94    inference(cnf_transformation,[],[f22])).
% 1.89/0.94  
% 1.89/0.94  fof(f42,plain,(
% 1.89/0.94    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.89/0.94    inference(equality_resolution,[],[f27])).
% 1.89/0.94  
% 1.89/0.94  fof(f5,axiom,(
% 1.89/0.94    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.89/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.94  
% 1.89/0.94  fof(f13,plain,(
% 1.89/0.94    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.89/0.94    inference(ennf_transformation,[],[f5])).
% 1.89/0.94  
% 1.89/0.94  fof(f23,plain,(
% 1.89/0.94    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.89/0.94    inference(nnf_transformation,[],[f13])).
% 1.89/0.94  
% 1.89/0.94  fof(f33,plain,(
% 1.89/0.94    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.89/0.94    inference(cnf_transformation,[],[f23])).
% 1.89/0.94  
% 1.89/0.94  fof(f8,axiom,(
% 1.89/0.94    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.89/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.94  
% 1.89/0.94  fof(f17,plain,(
% 1.89/0.94    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.89/0.94    inference(ennf_transformation,[],[f8])).
% 1.89/0.94  
% 1.89/0.94  fof(f18,plain,(
% 1.89/0.94    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.89/0.94    inference(flattening,[],[f17])).
% 1.89/0.94  
% 1.89/0.94  fof(f36,plain,(
% 1.89/0.94    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.89/0.94    inference(cnf_transformation,[],[f18])).
% 1.89/0.94  
% 1.89/0.94  fof(f9,conjecture,(
% 1.89/0.94    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) = k1_xboole_0))),
% 1.89/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.94  
% 1.89/0.94  fof(f10,negated_conjecture,(
% 1.89/0.94    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) = k1_xboole_0))),
% 1.89/0.94    inference(negated_conjecture,[],[f9])).
% 1.89/0.94  
% 1.89/0.94  fof(f19,plain,(
% 1.89/0.94    ? [X0,X1,X2] : ((k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) != k1_xboole_0 & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 1.89/0.94    inference(ennf_transformation,[],[f10])).
% 1.89/0.94  
% 1.89/0.94  fof(f20,plain,(
% 1.89/0.94    ? [X0,X1,X2] : (k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) != k1_xboole_0 & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 1.89/0.94    inference(flattening,[],[f19])).
% 1.89/0.94  
% 1.89/0.94  fof(f24,plain,(
% 1.89/0.94    ? [X0,X1,X2] : (k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) != k1_xboole_0 & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) != k1_xboole_0 & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 1.89/0.94    introduced(choice_axiom,[])).
% 1.89/0.94  
% 1.89/0.94  fof(f25,plain,(
% 1.89/0.94    k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) != k1_xboole_0 & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 1.89/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f24])).
% 1.89/0.94  
% 1.89/0.94  fof(f37,plain,(
% 1.89/0.94    v1_relat_1(sK2)),
% 1.89/0.94    inference(cnf_transformation,[],[f25])).
% 1.89/0.94  
% 1.89/0.94  fof(f6,axiom,(
% 1.89/0.94    ! [X0,X1,X2] : (v1_relat_1(X2) => k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)))),
% 1.89/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.94  
% 1.89/0.94  fof(f14,plain,(
% 1.89/0.94    ! [X0,X1,X2] : (k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_relat_1(X2))),
% 1.89/0.94    inference(ennf_transformation,[],[f6])).
% 1.89/0.94  
% 1.89/0.94  fof(f34,plain,(
% 1.89/0.94    ( ! [X2,X0,X1] : (k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_relat_1(X2)) )),
% 1.89/0.94    inference(cnf_transformation,[],[f14])).
% 1.89/0.94  
% 1.89/0.94  fof(f38,plain,(
% 1.89/0.94    r1_tarski(sK0,sK1)),
% 1.89/0.94    inference(cnf_transformation,[],[f25])).
% 1.89/0.94  
% 1.89/0.94  fof(f3,axiom,(
% 1.89/0.94    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 1.89/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.94  
% 1.89/0.94  fof(f12,plain,(
% 1.89/0.94    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.89/0.94    inference(ennf_transformation,[],[f3])).
% 1.89/0.94  
% 1.89/0.94  fof(f30,plain,(
% 1.89/0.94    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.89/0.94    inference(cnf_transformation,[],[f12])).
% 1.89/0.94  
% 1.89/0.94  fof(f4,axiom,(
% 1.89/0.94    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.89/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.94  
% 1.89/0.94  fof(f31,plain,(
% 1.89/0.94    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.89/0.94    inference(cnf_transformation,[],[f4])).
% 1.89/0.94  
% 1.89/0.94  fof(f40,plain,(
% 1.89/0.94    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k6_subset_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.89/0.94    inference(definition_unfolding,[],[f30,f31])).
% 1.89/0.94  
% 1.89/0.94  fof(f1,axiom,(
% 1.89/0.94    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.89/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.94  
% 1.89/0.94  fof(f11,plain,(
% 1.89/0.94    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.89/0.94    inference(ennf_transformation,[],[f1])).
% 1.89/0.94  
% 1.89/0.94  fof(f26,plain,(
% 1.89/0.94    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.89/0.94    inference(cnf_transformation,[],[f11])).
% 1.89/0.94  
% 1.89/0.94  fof(f7,axiom,(
% 1.89/0.94    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0))),
% 1.89/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.89/0.94  
% 1.89/0.94  fof(f15,plain,(
% 1.89/0.94    ! [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.89/0.94    inference(ennf_transformation,[],[f7])).
% 1.89/0.94  
% 1.89/0.94  fof(f16,plain,(
% 1.89/0.94    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 1.89/0.94    inference(flattening,[],[f15])).
% 1.89/0.94  
% 1.89/0.94  fof(f35,plain,(
% 1.89/0.94    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 1.89/0.94    inference(cnf_transformation,[],[f16])).
% 1.89/0.94  
% 1.89/0.94  fof(f39,plain,(
% 1.89/0.94    k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) != k1_xboole_0),
% 1.89/0.94    inference(cnf_transformation,[],[f25])).
% 1.89/0.94  
% 1.89/0.94  cnf(c_3,plain,
% 1.89/0.94      ( r1_tarski(X0,X0) ),
% 1.89/0.94      inference(cnf_transformation,[],[f42]) ).
% 1.89/0.94  
% 1.89/0.94  cnf(c_393,plain,
% 1.89/0.94      ( r1_tarski(X0,X0) = iProver_top ),
% 1.89/0.94      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.89/0.94  
% 1.89/0.94  cnf(c_5,plain,
% 1.89/0.94      ( v4_relat_1(X0,X1)
% 1.89/0.94      | ~ r1_tarski(k1_relat_1(X0),X1)
% 1.89/0.94      | ~ v1_relat_1(X0) ),
% 1.89/0.94      inference(cnf_transformation,[],[f33]) ).
% 1.89/0.94  
% 1.89/0.94  cnf(c_9,plain,
% 1.89/0.94      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 1.89/0.94      inference(cnf_transformation,[],[f36]) ).
% 1.89/0.94  
% 1.89/0.94  cnf(c_132,plain,
% 1.89/0.94      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 1.89/0.94      | ~ v1_relat_1(X0)
% 1.89/0.94      | k7_relat_1(X0,X1) = X0 ),
% 1.89/0.94      inference(resolution,[status(thm)],[c_5,c_9]) ).
% 1.89/0.94  
% 1.89/0.94  cnf(c_12,negated_conjecture,
% 1.89/0.94      ( v1_relat_1(sK2) ),
% 1.89/0.94      inference(cnf_transformation,[],[f37]) ).
% 1.89/0.94  
% 1.89/0.94  cnf(c_151,plain,
% 1.89/0.94      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 1.89/0.94      | k7_relat_1(X0,X1) = X0
% 1.89/0.94      | sK2 != X0 ),
% 1.89/0.94      inference(resolution_lifted,[status(thm)],[c_132,c_12]) ).
% 1.89/0.94  
% 1.89/0.94  cnf(c_152,plain,
% 1.89/0.94      ( ~ r1_tarski(k1_relat_1(sK2),X0) | k7_relat_1(sK2,X0) = sK2 ),
% 1.89/0.94      inference(unflattening,[status(thm)],[c_151]) ).
% 1.89/0.94  
% 1.89/0.94  cnf(c_390,plain,
% 1.89/0.94      ( k7_relat_1(sK2,X0) = sK2
% 1.89/0.94      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 1.89/0.94      inference(predicate_to_equality,[status(thm)],[c_152]) ).
% 1.89/0.94  
% 1.89/0.94  cnf(c_570,plain,
% 1.89/0.94      ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
% 1.89/0.94      inference(superposition,[status(thm)],[c_393,c_390]) ).
% 1.89/0.94  
% 1.89/0.94  cnf(c_7,plain,
% 1.89/0.94      ( ~ v1_relat_1(X0)
% 1.89/0.94      | k6_subset_1(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k6_subset_1(X1,X2)) ),
% 1.89/0.94      inference(cnf_transformation,[],[f34]) ).
% 1.89/0.94  
% 1.89/0.94  cnf(c_163,plain,
% 1.89/0.94      ( k6_subset_1(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k6_subset_1(X1,X2))
% 1.89/0.94      | sK2 != X0 ),
% 1.89/0.94      inference(resolution_lifted,[status(thm)],[c_7,c_12]) ).
% 1.89/0.94  
% 1.89/0.94  cnf(c_164,plain,
% 1.89/0.94      ( k6_subset_1(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1)) = k7_relat_1(sK2,k6_subset_1(X0,X1)) ),
% 1.89/0.94      inference(unflattening,[status(thm)],[c_163]) ).
% 1.89/0.94  
% 1.89/0.94  cnf(c_617,plain,
% 1.89/0.94      ( k7_relat_1(sK2,k6_subset_1(k1_relat_1(sK2),X0)) = k6_subset_1(sK2,k7_relat_1(sK2,X0)) ),
% 1.89/0.94      inference(superposition,[status(thm)],[c_570,c_164]) ).
% 1.89/0.94  
% 1.89/0.94  cnf(c_11,negated_conjecture,
% 1.89/0.94      ( r1_tarski(sK0,sK1) ),
% 1.89/0.94      inference(cnf_transformation,[],[f38]) ).
% 1.89/0.94  
% 1.89/0.94  cnf(c_391,plain,
% 1.89/0.94      ( r1_tarski(sK0,sK1) = iProver_top ),
% 1.89/0.94      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.89/0.94  
% 1.89/0.94  cnf(c_4,plain,
% 1.89/0.94      ( ~ r1_tarski(X0,X1) | r1_xboole_0(X0,k6_subset_1(X2,X1)) ),
% 1.89/0.94      inference(cnf_transformation,[],[f40]) ).
% 1.89/0.94  
% 1.89/0.94  cnf(c_392,plain,
% 1.89/0.94      ( r1_tarski(X0,X1) != iProver_top
% 1.89/0.94      | r1_xboole_0(X0,k6_subset_1(X2,X1)) = iProver_top ),
% 1.89/0.94      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.89/0.94  
% 1.89/0.94  cnf(c_0,plain,
% 1.89/0.94      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 1.89/0.94      inference(cnf_transformation,[],[f26]) ).
% 1.89/0.94  
% 1.89/0.94  cnf(c_395,plain,
% 1.89/0.94      ( r1_xboole_0(X0,X1) != iProver_top
% 1.89/0.94      | r1_xboole_0(X1,X0) = iProver_top ),
% 1.89/0.94      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.89/0.94  
% 1.89/0.94  cnf(c_734,plain,
% 1.89/0.94      ( r1_tarski(X0,X1) != iProver_top
% 1.89/0.94      | r1_xboole_0(k6_subset_1(X2,X1),X0) = iProver_top ),
% 1.89/0.94      inference(superposition,[status(thm)],[c_392,c_395]) ).
% 1.89/0.94  
% 1.89/0.94  cnf(c_8,plain,
% 1.89/0.94      ( ~ r1_xboole_0(X0,X1)
% 1.89/0.94      | ~ v1_relat_1(X2)
% 1.89/0.94      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
% 1.89/0.94      inference(cnf_transformation,[],[f35]) ).
% 1.89/0.94  
% 1.89/0.94  cnf(c_169,plain,
% 1.89/0.94      ( ~ r1_xboole_0(X0,X1)
% 1.89/0.94      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
% 1.89/0.94      | sK2 != X2 ),
% 1.89/0.94      inference(resolution_lifted,[status(thm)],[c_8,c_12]) ).
% 1.89/0.94  
% 1.89/0.94  cnf(c_170,plain,
% 1.89/0.94      ( ~ r1_xboole_0(X0,X1)
% 1.89/0.94      | k7_relat_1(k7_relat_1(sK2,X0),X1) = k1_xboole_0 ),
% 1.89/0.94      inference(unflattening,[status(thm)],[c_169]) ).
% 1.89/0.94  
% 1.89/0.94  cnf(c_389,plain,
% 1.89/0.94      ( k7_relat_1(k7_relat_1(sK2,X0),X1) = k1_xboole_0
% 1.89/0.94      | r1_xboole_0(X0,X1) != iProver_top ),
% 1.89/0.94      inference(predicate_to_equality,[status(thm)],[c_170]) ).
% 1.89/0.94  
% 1.89/0.94  cnf(c_937,plain,
% 1.89/0.94      ( k7_relat_1(k7_relat_1(sK2,k6_subset_1(X0,X1)),X2) = k1_xboole_0
% 1.89/0.94      | r1_tarski(X2,X1) != iProver_top ),
% 1.89/0.94      inference(superposition,[status(thm)],[c_734,c_389]) ).
% 1.89/0.94  
% 1.89/0.94  cnf(c_2621,plain,
% 1.89/0.94      ( k7_relat_1(k7_relat_1(sK2,k6_subset_1(X0,sK1)),sK0) = k1_xboole_0 ),
% 1.89/0.94      inference(superposition,[status(thm)],[c_391,c_937]) ).
% 1.89/0.94  
% 1.89/0.94  cnf(c_2765,plain,
% 1.89/0.94      ( k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) = k1_xboole_0 ),
% 1.89/0.94      inference(superposition,[status(thm)],[c_617,c_2621]) ).
% 1.89/0.94  
% 1.89/0.94  cnf(c_10,negated_conjecture,
% 1.89/0.94      ( k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) != k1_xboole_0 ),
% 1.89/0.94      inference(cnf_transformation,[],[f39]) ).
% 1.89/0.94  
% 1.89/0.94  cnf(contradiction,plain,
% 1.89/0.94      ( $false ),
% 1.89/0.94      inference(minisat,[status(thm)],[c_2765,c_10]) ).
% 1.89/0.94  
% 1.89/0.94  
% 1.89/0.94  % SZS output end CNFRefutation for theBenchmark.p
% 1.89/0.94  
% 1.89/0.94  ------                               Statistics
% 1.89/0.94  
% 1.89/0.94  ------ General
% 1.89/0.94  
% 1.89/0.94  abstr_ref_over_cycles:                  0
% 1.89/0.94  abstr_ref_under_cycles:                 0
% 1.89/0.94  gc_basic_clause_elim:                   0
% 1.89/0.94  forced_gc_time:                         0
% 1.89/0.94  parsing_time:                           0.007
% 1.89/0.94  unif_index_cands_time:                  0.
% 1.89/0.94  unif_index_add_time:                    0.
% 1.89/0.94  orderings_time:                         0.
% 1.89/0.94  out_proof_time:                         0.006
% 1.89/0.94  total_time:                             0.143
% 1.89/0.94  num_of_symbols:                         42
% 1.89/0.94  num_of_terms:                           3384
% 1.89/0.94  
% 1.89/0.94  ------ Preprocessing
% 1.89/0.94  
% 1.89/0.94  num_of_splits:                          0
% 1.89/0.94  num_of_split_atoms:                     0
% 1.89/0.94  num_of_reused_defs:                     0
% 1.89/0.94  num_eq_ax_congr_red:                    6
% 1.89/0.94  num_of_sem_filtered_clauses:            1
% 1.89/0.94  num_of_subtypes:                        0
% 1.89/0.94  monotx_restored_types:                  0
% 1.89/0.94  sat_num_of_epr_types:                   0
% 1.89/0.94  sat_num_of_non_cyclic_types:            0
% 1.89/0.94  sat_guarded_non_collapsed_types:        0
% 1.89/0.94  num_pure_diseq_elim:                    0
% 1.89/0.94  simp_replaced_by:                       0
% 1.89/0.94  res_preprocessed:                       54
% 1.89/0.94  prep_upred:                             0
% 1.89/0.94  prep_unflattend:                        3
% 1.89/0.94  smt_new_axioms:                         0
% 1.89/0.94  pred_elim_cands:                        2
% 1.89/0.94  pred_elim:                              2
% 1.89/0.94  pred_elim_cl:                           3
% 1.89/0.94  pred_elim_cycles:                       4
% 1.89/0.94  merged_defs:                            0
% 1.89/0.94  merged_defs_ncl:                        0
% 1.89/0.94  bin_hyper_res:                          0
% 1.89/0.94  prep_cycles:                            4
% 1.89/0.94  pred_elim_time:                         0.001
% 1.89/0.94  splitting_time:                         0.
% 1.89/0.94  sem_filter_time:                        0.
% 1.89/0.94  monotx_time:                            0.
% 1.89/0.94  subtype_inf_time:                       0.
% 1.89/0.94  
% 1.89/0.94  ------ Problem properties
% 1.89/0.94  
% 1.89/0.94  clauses:                                9
% 1.89/0.94  conjectures:                            2
% 1.89/0.94  epr:                                    4
% 1.89/0.94  horn:                                   9
% 1.89/0.94  ground:                                 2
% 1.89/0.94  unary:                                  4
% 1.89/0.94  binary:                                 4
% 1.89/0.94  lits:                                   15
% 1.89/0.94  lits_eq:                                5
% 1.89/0.94  fd_pure:                                0
% 1.89/0.94  fd_pseudo:                              0
% 1.89/0.94  fd_cond:                                0
% 1.89/0.94  fd_pseudo_cond:                         1
% 1.89/0.94  ac_symbols:                             0
% 1.89/0.94  
% 1.89/0.94  ------ Propositional Solver
% 1.89/0.94  
% 1.89/0.94  prop_solver_calls:                      29
% 1.89/0.94  prop_fast_solver_calls:                 282
% 1.89/0.94  smt_solver_calls:                       0
% 1.89/0.94  smt_fast_solver_calls:                  0
% 1.89/0.94  prop_num_of_clauses:                    980
% 1.89/0.94  prop_preprocess_simplified:             2602
% 1.89/0.94  prop_fo_subsumed:                       0
% 1.89/0.94  prop_solver_time:                       0.
% 1.89/0.94  smt_solver_time:                        0.
% 1.89/0.94  smt_fast_solver_time:                   0.
% 1.89/0.94  prop_fast_solver_time:                  0.
% 1.89/0.94  prop_unsat_core_time:                   0.
% 1.89/0.94  
% 1.89/0.94  ------ QBF
% 1.89/0.94  
% 1.89/0.94  qbf_q_res:                              0
% 1.89/0.94  qbf_num_tautologies:                    0
% 1.89/0.94  qbf_prep_cycles:                        0
% 1.89/0.94  
% 1.89/0.94  ------ BMC1
% 1.89/0.94  
% 1.89/0.94  bmc1_current_bound:                     -1
% 1.89/0.94  bmc1_last_solved_bound:                 -1
% 1.89/0.94  bmc1_unsat_core_size:                   -1
% 1.89/0.94  bmc1_unsat_core_parents_size:           -1
% 1.89/0.94  bmc1_merge_next_fun:                    0
% 1.89/0.94  bmc1_unsat_core_clauses_time:           0.
% 1.89/0.94  
% 1.89/0.94  ------ Instantiation
% 1.89/0.94  
% 1.89/0.94  inst_num_of_clauses:                    286
% 1.89/0.94  inst_num_in_passive:                    81
% 1.89/0.94  inst_num_in_active:                     174
% 1.89/0.94  inst_num_in_unprocessed:                31
% 1.89/0.94  inst_num_of_loops:                      180
% 1.89/0.94  inst_num_of_learning_restarts:          0
% 1.89/0.94  inst_num_moves_active_passive:          2
% 1.89/0.94  inst_lit_activity:                      0
% 1.89/0.94  inst_lit_activity_moves:                0
% 1.89/0.94  inst_num_tautologies:                   0
% 1.89/0.94  inst_num_prop_implied:                  0
% 1.89/0.94  inst_num_existing_simplified:           0
% 1.89/0.94  inst_num_eq_res_simplified:             0
% 1.89/0.94  inst_num_child_elim:                    0
% 1.89/0.94  inst_num_of_dismatching_blockings:      113
% 1.89/0.94  inst_num_of_non_proper_insts:           431
% 1.89/0.94  inst_num_of_duplicates:                 0
% 1.89/0.94  inst_inst_num_from_inst_to_res:         0
% 1.89/0.94  inst_dismatching_checking_time:         0.
% 1.89/0.94  
% 1.89/0.94  ------ Resolution
% 1.89/0.94  
% 1.89/0.94  res_num_of_clauses:                     0
% 1.89/0.94  res_num_in_passive:                     0
% 1.89/0.94  res_num_in_active:                      0
% 1.89/0.94  res_num_of_loops:                       58
% 1.89/0.94  res_forward_subset_subsumed:            106
% 1.89/0.94  res_backward_subset_subsumed:           0
% 1.89/0.94  res_forward_subsumed:                   0
% 1.89/0.94  res_backward_subsumed:                  0
% 1.89/0.94  res_forward_subsumption_resolution:     0
% 1.89/0.94  res_backward_subsumption_resolution:    0
% 1.89/0.94  res_clause_to_clause_subsumption:       304
% 1.89/0.94  res_orphan_elimination:                 0
% 1.89/0.94  res_tautology_del:                      46
% 1.89/0.94  res_num_eq_res_simplified:              0
% 1.89/0.94  res_num_sel_changes:                    0
% 1.89/0.94  res_moves_from_active_to_pass:          0
% 1.89/0.94  
% 1.89/0.94  ------ Superposition
% 1.89/0.94  
% 1.89/0.94  sup_time_total:                         0.
% 1.89/0.94  sup_time_generating:                    0.
% 1.89/0.94  sup_time_sim_full:                      0.
% 1.89/0.94  sup_time_sim_immed:                     0.
% 1.89/0.94  
% 1.89/0.94  sup_num_of_clauses:                     104
% 1.89/0.94  sup_num_in_active:                      36
% 1.89/0.94  sup_num_in_passive:                     68
% 1.89/0.94  sup_num_of_loops:                       35
% 1.89/0.94  sup_fw_superposition:                   139
% 1.89/0.94  sup_bw_superposition:                   37
% 1.89/0.94  sup_immediate_simplified:               55
% 1.89/0.94  sup_given_eliminated:                   0
% 1.89/0.94  comparisons_done:                       0
% 1.89/0.94  comparisons_avoided:                    0
% 1.89/0.94  
% 1.89/0.94  ------ Simplifications
% 1.89/0.94  
% 1.89/0.94  
% 1.89/0.94  sim_fw_subset_subsumed:                 0
% 1.89/0.94  sim_bw_subset_subsumed:                 0
% 1.89/0.94  sim_fw_subsumed:                        31
% 1.89/0.94  sim_bw_subsumed:                        24
% 1.89/0.94  sim_fw_subsumption_res:                 0
% 1.89/0.94  sim_bw_subsumption_res:                 0
% 1.89/0.94  sim_tautology_del:                      0
% 1.89/0.94  sim_eq_tautology_del:                   2
% 1.89/0.94  sim_eq_res_simp:                        0
% 1.89/0.94  sim_fw_demodulated:                     1
% 1.89/0.94  sim_bw_demodulated:                     0
% 1.89/0.94  sim_light_normalised:                   17
% 1.89/0.94  sim_joinable_taut:                      0
% 1.89/0.94  sim_joinable_simp:                      0
% 1.89/0.94  sim_ac_normalised:                      0
% 1.89/0.94  sim_smt_subsumption:                    0
% 1.89/0.94  
%------------------------------------------------------------------------------
