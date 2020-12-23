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
% DateTime   : Thu Dec  3 11:45:18 EST 2020

% Result     : Theorem 0.94s
% Output     : CNFRefutation 0.94s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 111 expanded)
%              Number of clauses        :   22 (  22 expanded)
%              Number of leaves         :   19 (  32 expanded)
%              Depth                    :   17
%              Number of atoms          :  103 ( 140 expanded)
%              Number of equality atoms :   66 ( 103 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f14])).

fof(f20,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK0(X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK0(X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f23])).

fof(f40,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f35,f44])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f34,f45])).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f33,f46])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f47])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f38,f48])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f39,f48])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k2_zfmisc_1(X0,k2_relat_1(X1)))) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f42,f49])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f28,f49])).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f29,f50])).

fof(f16,conjecture,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f16])).

fof(f22,plain,(
    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f17])).

fof(f25,plain,
    ( ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k7_relat_1(k1_xboole_0,sK1) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f25])).

fof(f43,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_6,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_76,plain,
    ( ~ r2_hidden(X0,X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) != X3
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_4])).

cnf(c_77,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_76])).

cnf(c_87,plain,
    ( v1_relat_1(X0)
    | sK0(X0) != X1
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_77])).

cnf(c_88,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_87])).

cnf(c_232,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_88])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(X1,k2_relat_1(X0)))) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_233,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(X1,k2_relat_1(X0)))) = k7_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_444,plain,
    ( k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_zfmisc_1(X0,k2_relat_1(k1_xboole_0)))) = k7_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_232,c_233])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_280,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_1,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_380,plain,
    ( k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_280,c_1])).

cnf(c_445,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_444,c_380])).

cnf(c_8,negated_conjecture,
    ( k1_xboole_0 != k7_relat_1(k1_xboole_0,sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_448,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_445,c_8])).

cnf(c_158,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_172,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_158])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_448,c_172])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:35:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.94/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.94/1.02  
% 0.94/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.94/1.02  
% 0.94/1.02  ------  iProver source info
% 0.94/1.02  
% 0.94/1.02  git: date: 2020-06-30 10:37:57 +0100
% 0.94/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.94/1.02  git: non_committed_changes: false
% 0.94/1.02  git: last_make_outside_of_git: false
% 0.94/1.02  
% 0.94/1.02  ------ 
% 0.94/1.02  
% 0.94/1.02  ------ Input Options
% 0.94/1.02  
% 0.94/1.02  --out_options                           all
% 0.94/1.02  --tptp_safe_out                         true
% 0.94/1.02  --problem_path                          ""
% 0.94/1.02  --include_path                          ""
% 0.94/1.02  --clausifier                            res/vclausify_rel
% 0.94/1.02  --clausifier_options                    --mode clausify
% 0.94/1.02  --stdin                                 false
% 0.94/1.02  --stats_out                             all
% 0.94/1.02  
% 0.94/1.02  ------ General Options
% 0.94/1.02  
% 0.94/1.02  --fof                                   false
% 0.94/1.02  --time_out_real                         305.
% 0.94/1.02  --time_out_virtual                      -1.
% 0.94/1.02  --symbol_type_check                     false
% 0.94/1.02  --clausify_out                          false
% 0.94/1.02  --sig_cnt_out                           false
% 0.94/1.02  --trig_cnt_out                          false
% 0.94/1.02  --trig_cnt_out_tolerance                1.
% 0.94/1.02  --trig_cnt_out_sk_spl                   false
% 0.94/1.02  --abstr_cl_out                          false
% 0.94/1.02  
% 0.94/1.02  ------ Global Options
% 0.94/1.02  
% 0.94/1.02  --schedule                              default
% 0.94/1.02  --add_important_lit                     false
% 0.94/1.02  --prop_solver_per_cl                    1000
% 0.94/1.02  --min_unsat_core                        false
% 0.94/1.02  --soft_assumptions                      false
% 0.94/1.02  --soft_lemma_size                       3
% 0.94/1.02  --prop_impl_unit_size                   0
% 0.94/1.02  --prop_impl_unit                        []
% 0.94/1.02  --share_sel_clauses                     true
% 0.94/1.02  --reset_solvers                         false
% 0.94/1.02  --bc_imp_inh                            [conj_cone]
% 0.94/1.02  --conj_cone_tolerance                   3.
% 0.94/1.02  --extra_neg_conj                        none
% 0.94/1.02  --large_theory_mode                     true
% 0.94/1.02  --prolific_symb_bound                   200
% 0.94/1.02  --lt_threshold                          2000
% 0.94/1.02  --clause_weak_htbl                      true
% 0.94/1.02  --gc_record_bc_elim                     false
% 0.94/1.02  
% 0.94/1.02  ------ Preprocessing Options
% 0.94/1.02  
% 0.94/1.02  --preprocessing_flag                    true
% 0.94/1.02  --time_out_prep_mult                    0.1
% 0.94/1.02  --splitting_mode                        input
% 0.94/1.02  --splitting_grd                         true
% 0.94/1.02  --splitting_cvd                         false
% 0.94/1.02  --splitting_cvd_svl                     false
% 0.94/1.02  --splitting_nvd                         32
% 0.94/1.02  --sub_typing                            true
% 0.94/1.02  --prep_gs_sim                           true
% 0.94/1.02  --prep_unflatten                        true
% 0.94/1.02  --prep_res_sim                          true
% 0.94/1.02  --prep_upred                            true
% 0.94/1.02  --prep_sem_filter                       exhaustive
% 0.94/1.02  --prep_sem_filter_out                   false
% 0.94/1.02  --pred_elim                             true
% 0.94/1.02  --res_sim_input                         true
% 0.94/1.02  --eq_ax_congr_red                       true
% 0.94/1.02  --pure_diseq_elim                       true
% 0.94/1.02  --brand_transform                       false
% 0.94/1.02  --non_eq_to_eq                          false
% 0.94/1.02  --prep_def_merge                        true
% 0.94/1.02  --prep_def_merge_prop_impl              false
% 0.94/1.02  --prep_def_merge_mbd                    true
% 0.94/1.02  --prep_def_merge_tr_red                 false
% 0.94/1.02  --prep_def_merge_tr_cl                  false
% 0.94/1.02  --smt_preprocessing                     true
% 0.94/1.02  --smt_ac_axioms                         fast
% 0.94/1.02  --preprocessed_out                      false
% 0.94/1.02  --preprocessed_stats                    false
% 0.94/1.02  
% 0.94/1.02  ------ Abstraction refinement Options
% 0.94/1.02  
% 0.94/1.02  --abstr_ref                             []
% 0.94/1.02  --abstr_ref_prep                        false
% 0.94/1.02  --abstr_ref_until_sat                   false
% 0.94/1.02  --abstr_ref_sig_restrict                funpre
% 0.94/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 0.94/1.02  --abstr_ref_under                       []
% 0.94/1.02  
% 0.94/1.02  ------ SAT Options
% 0.94/1.02  
% 0.94/1.02  --sat_mode                              false
% 0.94/1.02  --sat_fm_restart_options                ""
% 0.94/1.02  --sat_gr_def                            false
% 0.94/1.02  --sat_epr_types                         true
% 0.94/1.02  --sat_non_cyclic_types                  false
% 0.94/1.02  --sat_finite_models                     false
% 0.94/1.02  --sat_fm_lemmas                         false
% 0.94/1.02  --sat_fm_prep                           false
% 0.94/1.02  --sat_fm_uc_incr                        true
% 0.94/1.02  --sat_out_model                         small
% 0.94/1.02  --sat_out_clauses                       false
% 0.94/1.02  
% 0.94/1.02  ------ QBF Options
% 0.94/1.02  
% 0.94/1.02  --qbf_mode                              false
% 0.94/1.02  --qbf_elim_univ                         false
% 0.94/1.02  --qbf_dom_inst                          none
% 0.94/1.02  --qbf_dom_pre_inst                      false
% 0.94/1.02  --qbf_sk_in                             false
% 0.94/1.02  --qbf_pred_elim                         true
% 0.94/1.02  --qbf_split                             512
% 0.94/1.02  
% 0.94/1.02  ------ BMC1 Options
% 0.94/1.02  
% 0.94/1.02  --bmc1_incremental                      false
% 0.94/1.02  --bmc1_axioms                           reachable_all
% 0.94/1.02  --bmc1_min_bound                        0
% 0.94/1.02  --bmc1_max_bound                        -1
% 0.94/1.02  --bmc1_max_bound_default                -1
% 0.94/1.02  --bmc1_symbol_reachability              true
% 0.94/1.02  --bmc1_property_lemmas                  false
% 0.94/1.02  --bmc1_k_induction                      false
% 0.94/1.02  --bmc1_non_equiv_states                 false
% 0.94/1.02  --bmc1_deadlock                         false
% 0.94/1.02  --bmc1_ucm                              false
% 0.94/1.02  --bmc1_add_unsat_core                   none
% 0.94/1.02  --bmc1_unsat_core_children              false
% 0.94/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 0.94/1.02  --bmc1_out_stat                         full
% 0.94/1.02  --bmc1_ground_init                      false
% 0.94/1.02  --bmc1_pre_inst_next_state              false
% 0.94/1.02  --bmc1_pre_inst_state                   false
% 0.94/1.02  --bmc1_pre_inst_reach_state             false
% 0.94/1.02  --bmc1_out_unsat_core                   false
% 0.94/1.02  --bmc1_aig_witness_out                  false
% 0.94/1.02  --bmc1_verbose                          false
% 0.94/1.02  --bmc1_dump_clauses_tptp                false
% 0.94/1.02  --bmc1_dump_unsat_core_tptp             false
% 0.94/1.02  --bmc1_dump_file                        -
% 0.94/1.02  --bmc1_ucm_expand_uc_limit              128
% 0.94/1.02  --bmc1_ucm_n_expand_iterations          6
% 0.94/1.02  --bmc1_ucm_extend_mode                  1
% 0.94/1.02  --bmc1_ucm_init_mode                    2
% 0.94/1.02  --bmc1_ucm_cone_mode                    none
% 0.94/1.02  --bmc1_ucm_reduced_relation_type        0
% 0.94/1.02  --bmc1_ucm_relax_model                  4
% 0.94/1.02  --bmc1_ucm_full_tr_after_sat            true
% 0.94/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 0.94/1.02  --bmc1_ucm_layered_model                none
% 0.94/1.02  --bmc1_ucm_max_lemma_size               10
% 0.94/1.02  
% 0.94/1.02  ------ AIG Options
% 0.94/1.02  
% 0.94/1.02  --aig_mode                              false
% 0.94/1.02  
% 0.94/1.02  ------ Instantiation Options
% 0.94/1.02  
% 0.94/1.02  --instantiation_flag                    true
% 0.94/1.02  --inst_sos_flag                         false
% 0.94/1.02  --inst_sos_phase                        true
% 0.94/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.94/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.94/1.02  --inst_lit_sel_side                     num_symb
% 0.94/1.02  --inst_solver_per_active                1400
% 0.94/1.02  --inst_solver_calls_frac                1.
% 0.94/1.02  --inst_passive_queue_type               priority_queues
% 0.94/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.94/1.02  --inst_passive_queues_freq              [25;2]
% 0.94/1.02  --inst_dismatching                      true
% 0.94/1.02  --inst_eager_unprocessed_to_passive     true
% 0.94/1.02  --inst_prop_sim_given                   true
% 0.94/1.02  --inst_prop_sim_new                     false
% 0.94/1.02  --inst_subs_new                         false
% 0.94/1.02  --inst_eq_res_simp                      false
% 0.94/1.02  --inst_subs_given                       false
% 0.94/1.02  --inst_orphan_elimination               true
% 0.94/1.02  --inst_learning_loop_flag               true
% 0.94/1.02  --inst_learning_start                   3000
% 0.94/1.02  --inst_learning_factor                  2
% 0.94/1.02  --inst_start_prop_sim_after_learn       3
% 0.94/1.02  --inst_sel_renew                        solver
% 0.94/1.02  --inst_lit_activity_flag                true
% 0.94/1.02  --inst_restr_to_given                   false
% 0.94/1.02  --inst_activity_threshold               500
% 0.94/1.02  --inst_out_proof                        true
% 0.94/1.02  
% 0.94/1.02  ------ Resolution Options
% 0.94/1.02  
% 0.94/1.02  --resolution_flag                       true
% 0.94/1.02  --res_lit_sel                           adaptive
% 0.94/1.02  --res_lit_sel_side                      none
% 0.94/1.02  --res_ordering                          kbo
% 0.94/1.02  --res_to_prop_solver                    active
% 0.94/1.02  --res_prop_simpl_new                    false
% 0.94/1.02  --res_prop_simpl_given                  true
% 0.94/1.02  --res_passive_queue_type                priority_queues
% 0.94/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.94/1.02  --res_passive_queues_freq               [15;5]
% 0.94/1.02  --res_forward_subs                      full
% 0.94/1.02  --res_backward_subs                     full
% 0.94/1.02  --res_forward_subs_resolution           true
% 0.94/1.02  --res_backward_subs_resolution          true
% 0.94/1.02  --res_orphan_elimination                true
% 0.94/1.02  --res_time_limit                        2.
% 0.94/1.02  --res_out_proof                         true
% 0.94/1.02  
% 0.94/1.02  ------ Superposition Options
% 0.94/1.02  
% 0.94/1.02  --superposition_flag                    true
% 0.94/1.02  --sup_passive_queue_type                priority_queues
% 0.94/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.94/1.02  --sup_passive_queues_freq               [8;1;4]
% 0.94/1.02  --demod_completeness_check              fast
% 0.94/1.02  --demod_use_ground                      true
% 0.94/1.02  --sup_to_prop_solver                    passive
% 0.94/1.02  --sup_prop_simpl_new                    true
% 0.94/1.02  --sup_prop_simpl_given                  true
% 0.94/1.02  --sup_fun_splitting                     false
% 0.94/1.02  --sup_smt_interval                      50000
% 0.94/1.02  
% 0.94/1.02  ------ Superposition Simplification Setup
% 0.94/1.02  
% 0.94/1.02  --sup_indices_passive                   []
% 0.94/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.94/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.94/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.94/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 0.94/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.94/1.02  --sup_full_bw                           [BwDemod]
% 0.94/1.02  --sup_immed_triv                        [TrivRules]
% 0.94/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.94/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.94/1.02  --sup_immed_bw_main                     []
% 0.94/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.94/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 0.94/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.94/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.94/1.02  
% 0.94/1.02  ------ Combination Options
% 0.94/1.02  
% 0.94/1.02  --comb_res_mult                         3
% 0.94/1.02  --comb_sup_mult                         2
% 0.94/1.02  --comb_inst_mult                        10
% 0.94/1.02  
% 0.94/1.02  ------ Debug Options
% 0.94/1.02  
% 0.94/1.02  --dbg_backtrace                         false
% 0.94/1.02  --dbg_dump_prop_clauses                 false
% 0.94/1.02  --dbg_dump_prop_clauses_file            -
% 0.94/1.02  --dbg_out_stat                          false
% 0.94/1.02  ------ Parsing...
% 0.94/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.94/1.02  
% 0.94/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 0.94/1.02  
% 0.94/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.94/1.02  
% 0.94/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.94/1.02  ------ Proving...
% 0.94/1.02  ------ Problem Properties 
% 0.94/1.02  
% 0.94/1.02  
% 0.94/1.02  clauses                                 7
% 0.94/1.02  conjectures                             1
% 0.94/1.02  EPR                                     1
% 0.94/1.02  Horn                                    7
% 0.94/1.02  unary                                   5
% 0.94/1.02  binary                                  2
% 0.94/1.02  lits                                    9
% 0.94/1.02  lits eq                                 6
% 0.94/1.02  fd_pure                                 0
% 0.94/1.02  fd_pseudo                               0
% 0.94/1.02  fd_cond                                 0
% 0.94/1.02  fd_pseudo_cond                          0
% 0.94/1.02  AC symbols                              0
% 0.94/1.02  
% 0.94/1.02  ------ Schedule dynamic 5 is on 
% 0.94/1.02  
% 0.94/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.94/1.02  
% 0.94/1.02  
% 0.94/1.02  ------ 
% 0.94/1.02  Current options:
% 0.94/1.02  ------ 
% 0.94/1.02  
% 0.94/1.02  ------ Input Options
% 0.94/1.02  
% 0.94/1.02  --out_options                           all
% 0.94/1.02  --tptp_safe_out                         true
% 0.94/1.02  --problem_path                          ""
% 0.94/1.02  --include_path                          ""
% 0.94/1.02  --clausifier                            res/vclausify_rel
% 0.94/1.02  --clausifier_options                    --mode clausify
% 0.94/1.02  --stdin                                 false
% 0.94/1.02  --stats_out                             all
% 0.94/1.02  
% 0.94/1.02  ------ General Options
% 0.94/1.02  
% 0.94/1.02  --fof                                   false
% 0.94/1.02  --time_out_real                         305.
% 0.94/1.02  --time_out_virtual                      -1.
% 0.94/1.02  --symbol_type_check                     false
% 0.94/1.02  --clausify_out                          false
% 0.94/1.02  --sig_cnt_out                           false
% 0.94/1.02  --trig_cnt_out                          false
% 0.94/1.02  --trig_cnt_out_tolerance                1.
% 0.94/1.02  --trig_cnt_out_sk_spl                   false
% 0.94/1.02  --abstr_cl_out                          false
% 0.94/1.02  
% 0.94/1.02  ------ Global Options
% 0.94/1.02  
% 0.94/1.02  --schedule                              default
% 0.94/1.02  --add_important_lit                     false
% 0.94/1.02  --prop_solver_per_cl                    1000
% 0.94/1.02  --min_unsat_core                        false
% 0.94/1.02  --soft_assumptions                      false
% 0.94/1.02  --soft_lemma_size                       3
% 0.94/1.02  --prop_impl_unit_size                   0
% 0.94/1.02  --prop_impl_unit                        []
% 0.94/1.02  --share_sel_clauses                     true
% 0.94/1.02  --reset_solvers                         false
% 0.94/1.02  --bc_imp_inh                            [conj_cone]
% 0.94/1.02  --conj_cone_tolerance                   3.
% 0.94/1.02  --extra_neg_conj                        none
% 0.94/1.02  --large_theory_mode                     true
% 0.94/1.02  --prolific_symb_bound                   200
% 0.94/1.02  --lt_threshold                          2000
% 0.94/1.02  --clause_weak_htbl                      true
% 0.94/1.02  --gc_record_bc_elim                     false
% 0.94/1.02  
% 0.94/1.02  ------ Preprocessing Options
% 0.94/1.02  
% 0.94/1.02  --preprocessing_flag                    true
% 0.94/1.02  --time_out_prep_mult                    0.1
% 0.94/1.02  --splitting_mode                        input
% 0.94/1.02  --splitting_grd                         true
% 0.94/1.02  --splitting_cvd                         false
% 0.94/1.02  --splitting_cvd_svl                     false
% 0.94/1.02  --splitting_nvd                         32
% 0.94/1.02  --sub_typing                            true
% 0.94/1.02  --prep_gs_sim                           true
% 0.94/1.02  --prep_unflatten                        true
% 0.94/1.02  --prep_res_sim                          true
% 0.94/1.02  --prep_upred                            true
% 0.94/1.02  --prep_sem_filter                       exhaustive
% 0.94/1.02  --prep_sem_filter_out                   false
% 0.94/1.02  --pred_elim                             true
% 0.94/1.02  --res_sim_input                         true
% 0.94/1.02  --eq_ax_congr_red                       true
% 0.94/1.02  --pure_diseq_elim                       true
% 0.94/1.02  --brand_transform                       false
% 0.94/1.02  --non_eq_to_eq                          false
% 0.94/1.02  --prep_def_merge                        true
% 0.94/1.02  --prep_def_merge_prop_impl              false
% 0.94/1.02  --prep_def_merge_mbd                    true
% 0.94/1.02  --prep_def_merge_tr_red                 false
% 0.94/1.02  --prep_def_merge_tr_cl                  false
% 0.94/1.02  --smt_preprocessing                     true
% 0.94/1.02  --smt_ac_axioms                         fast
% 0.94/1.02  --preprocessed_out                      false
% 0.94/1.02  --preprocessed_stats                    false
% 0.94/1.02  
% 0.94/1.02  ------ Abstraction refinement Options
% 0.94/1.02  
% 0.94/1.02  --abstr_ref                             []
% 0.94/1.02  --abstr_ref_prep                        false
% 0.94/1.02  --abstr_ref_until_sat                   false
% 0.94/1.02  --abstr_ref_sig_restrict                funpre
% 0.94/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 0.94/1.02  --abstr_ref_under                       []
% 0.94/1.02  
% 0.94/1.02  ------ SAT Options
% 0.94/1.02  
% 0.94/1.02  --sat_mode                              false
% 0.94/1.02  --sat_fm_restart_options                ""
% 0.94/1.02  --sat_gr_def                            false
% 0.94/1.02  --sat_epr_types                         true
% 0.94/1.02  --sat_non_cyclic_types                  false
% 0.94/1.02  --sat_finite_models                     false
% 0.94/1.02  --sat_fm_lemmas                         false
% 0.94/1.02  --sat_fm_prep                           false
% 0.94/1.02  --sat_fm_uc_incr                        true
% 0.94/1.02  --sat_out_model                         small
% 0.94/1.02  --sat_out_clauses                       false
% 0.94/1.02  
% 0.94/1.02  ------ QBF Options
% 0.94/1.02  
% 0.94/1.02  --qbf_mode                              false
% 0.94/1.02  --qbf_elim_univ                         false
% 0.94/1.02  --qbf_dom_inst                          none
% 0.94/1.02  --qbf_dom_pre_inst                      false
% 0.94/1.02  --qbf_sk_in                             false
% 0.94/1.02  --qbf_pred_elim                         true
% 0.94/1.02  --qbf_split                             512
% 0.94/1.02  
% 0.94/1.02  ------ BMC1 Options
% 0.94/1.02  
% 0.94/1.02  --bmc1_incremental                      false
% 0.94/1.02  --bmc1_axioms                           reachable_all
% 0.94/1.02  --bmc1_min_bound                        0
% 0.94/1.02  --bmc1_max_bound                        -1
% 0.94/1.02  --bmc1_max_bound_default                -1
% 0.94/1.02  --bmc1_symbol_reachability              true
% 0.94/1.02  --bmc1_property_lemmas                  false
% 0.94/1.02  --bmc1_k_induction                      false
% 0.94/1.02  --bmc1_non_equiv_states                 false
% 0.94/1.02  --bmc1_deadlock                         false
% 0.94/1.02  --bmc1_ucm                              false
% 0.94/1.02  --bmc1_add_unsat_core                   none
% 0.94/1.02  --bmc1_unsat_core_children              false
% 0.94/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 0.94/1.02  --bmc1_out_stat                         full
% 0.94/1.02  --bmc1_ground_init                      false
% 0.94/1.02  --bmc1_pre_inst_next_state              false
% 0.94/1.02  --bmc1_pre_inst_state                   false
% 0.94/1.02  --bmc1_pre_inst_reach_state             false
% 0.94/1.02  --bmc1_out_unsat_core                   false
% 0.94/1.02  --bmc1_aig_witness_out                  false
% 0.94/1.02  --bmc1_verbose                          false
% 0.94/1.02  --bmc1_dump_clauses_tptp                false
% 0.94/1.02  --bmc1_dump_unsat_core_tptp             false
% 0.94/1.02  --bmc1_dump_file                        -
% 0.94/1.02  --bmc1_ucm_expand_uc_limit              128
% 0.94/1.02  --bmc1_ucm_n_expand_iterations          6
% 0.94/1.02  --bmc1_ucm_extend_mode                  1
% 0.94/1.02  --bmc1_ucm_init_mode                    2
% 0.94/1.02  --bmc1_ucm_cone_mode                    none
% 0.94/1.02  --bmc1_ucm_reduced_relation_type        0
% 0.94/1.02  --bmc1_ucm_relax_model                  4
% 0.94/1.02  --bmc1_ucm_full_tr_after_sat            true
% 0.94/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 0.94/1.02  --bmc1_ucm_layered_model                none
% 0.94/1.02  --bmc1_ucm_max_lemma_size               10
% 0.94/1.02  
% 0.94/1.02  ------ AIG Options
% 0.94/1.02  
% 0.94/1.02  --aig_mode                              false
% 0.94/1.02  
% 0.94/1.02  ------ Instantiation Options
% 0.94/1.02  
% 0.94/1.02  --instantiation_flag                    true
% 0.94/1.02  --inst_sos_flag                         false
% 0.94/1.02  --inst_sos_phase                        true
% 0.94/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.94/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.94/1.02  --inst_lit_sel_side                     none
% 0.94/1.02  --inst_solver_per_active                1400
% 0.94/1.02  --inst_solver_calls_frac                1.
% 0.94/1.02  --inst_passive_queue_type               priority_queues
% 0.94/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.94/1.02  --inst_passive_queues_freq              [25;2]
% 0.94/1.02  --inst_dismatching                      true
% 0.94/1.02  --inst_eager_unprocessed_to_passive     true
% 0.94/1.02  --inst_prop_sim_given                   true
% 0.94/1.02  --inst_prop_sim_new                     false
% 0.94/1.02  --inst_subs_new                         false
% 0.94/1.02  --inst_eq_res_simp                      false
% 0.94/1.02  --inst_subs_given                       false
% 0.94/1.02  --inst_orphan_elimination               true
% 0.94/1.02  --inst_learning_loop_flag               true
% 0.94/1.02  --inst_learning_start                   3000
% 0.94/1.02  --inst_learning_factor                  2
% 0.94/1.02  --inst_start_prop_sim_after_learn       3
% 0.94/1.02  --inst_sel_renew                        solver
% 0.94/1.02  --inst_lit_activity_flag                true
% 0.94/1.02  --inst_restr_to_given                   false
% 0.94/1.02  --inst_activity_threshold               500
% 0.94/1.02  --inst_out_proof                        true
% 0.94/1.02  
% 0.94/1.02  ------ Resolution Options
% 0.94/1.02  
% 0.94/1.02  --resolution_flag                       false
% 0.94/1.02  --res_lit_sel                           adaptive
% 0.94/1.02  --res_lit_sel_side                      none
% 0.94/1.02  --res_ordering                          kbo
% 0.94/1.02  --res_to_prop_solver                    active
% 0.94/1.02  --res_prop_simpl_new                    false
% 0.94/1.02  --res_prop_simpl_given                  true
% 0.94/1.02  --res_passive_queue_type                priority_queues
% 0.94/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.94/1.02  --res_passive_queues_freq               [15;5]
% 0.94/1.02  --res_forward_subs                      full
% 0.94/1.02  --res_backward_subs                     full
% 0.94/1.02  --res_forward_subs_resolution           true
% 0.94/1.02  --res_backward_subs_resolution          true
% 0.94/1.02  --res_orphan_elimination                true
% 0.94/1.02  --res_time_limit                        2.
% 0.94/1.02  --res_out_proof                         true
% 0.94/1.02  
% 0.94/1.02  ------ Superposition Options
% 0.94/1.02  
% 0.94/1.02  --superposition_flag                    true
% 0.94/1.02  --sup_passive_queue_type                priority_queues
% 0.94/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.94/1.02  --sup_passive_queues_freq               [8;1;4]
% 0.94/1.02  --demod_completeness_check              fast
% 0.94/1.02  --demod_use_ground                      true
% 0.94/1.02  --sup_to_prop_solver                    passive
% 0.94/1.02  --sup_prop_simpl_new                    true
% 0.94/1.02  --sup_prop_simpl_given                  true
% 0.94/1.02  --sup_fun_splitting                     false
% 0.94/1.02  --sup_smt_interval                      50000
% 0.94/1.02  
% 0.94/1.02  ------ Superposition Simplification Setup
% 0.94/1.02  
% 0.94/1.02  --sup_indices_passive                   []
% 0.94/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.94/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.94/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.94/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 0.94/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.94/1.02  --sup_full_bw                           [BwDemod]
% 0.94/1.02  --sup_immed_triv                        [TrivRules]
% 0.94/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.94/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.94/1.02  --sup_immed_bw_main                     []
% 0.94/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.94/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 0.94/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.94/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.94/1.02  
% 0.94/1.02  ------ Combination Options
% 0.94/1.02  
% 0.94/1.02  --comb_res_mult                         3
% 0.94/1.02  --comb_sup_mult                         2
% 0.94/1.02  --comb_inst_mult                        10
% 0.94/1.02  
% 0.94/1.02  ------ Debug Options
% 0.94/1.02  
% 0.94/1.02  --dbg_backtrace                         false
% 0.94/1.02  --dbg_dump_prop_clauses                 false
% 0.94/1.02  --dbg_dump_prop_clauses_file            -
% 0.94/1.02  --dbg_out_stat                          false
% 0.94/1.02  
% 0.94/1.02  
% 0.94/1.02  
% 0.94/1.02  
% 0.94/1.02  ------ Proving...
% 0.94/1.02  
% 0.94/1.02  
% 0.94/1.02  % SZS status Theorem for theBenchmark.p
% 0.94/1.02  
% 0.94/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 0.94/1.02  
% 0.94/1.02  fof(f14,axiom,(
% 0.94/1.02    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.94/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.02  
% 0.94/1.02  fof(f18,plain,(
% 0.94/1.02    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 0.94/1.02    inference(unused_predicate_definition_removal,[],[f14])).
% 0.94/1.02  
% 0.94/1.02  fof(f20,plain,(
% 0.94/1.02    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.94/1.02    inference(ennf_transformation,[],[f18])).
% 0.94/1.02  
% 0.94/1.02  fof(f23,plain,(
% 0.94/1.02    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0)))),
% 0.94/1.02    introduced(choice_axiom,[])).
% 0.94/1.02  
% 0.94/1.02  fof(f24,plain,(
% 0.94/1.02    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0)))),
% 0.94/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f23])).
% 0.94/1.02  
% 0.94/1.02  fof(f40,plain,(
% 0.94/1.02    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK0(X0),X0)) )),
% 0.94/1.02    inference(cnf_transformation,[],[f24])).
% 0.94/1.02  
% 0.94/1.02  fof(f5,axiom,(
% 0.94/1.02    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.94/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.02  
% 0.94/1.02  fof(f31,plain,(
% 0.94/1.02    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.94/1.02    inference(cnf_transformation,[],[f5])).
% 0.94/1.02  
% 0.94/1.02  fof(f12,axiom,(
% 0.94/1.02    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.94/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.02  
% 0.94/1.02  fof(f19,plain,(
% 0.94/1.02    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.94/1.02    inference(ennf_transformation,[],[f12])).
% 0.94/1.02  
% 0.94/1.02  fof(f38,plain,(
% 0.94/1.02    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.94/1.02    inference(cnf_transformation,[],[f19])).
% 0.94/1.02  
% 0.94/1.02  fof(f6,axiom,(
% 0.94/1.02    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.94/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.02  
% 0.94/1.02  fof(f32,plain,(
% 0.94/1.02    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.94/1.02    inference(cnf_transformation,[],[f6])).
% 0.94/1.02  
% 0.94/1.02  fof(f7,axiom,(
% 0.94/1.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.94/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.02  
% 0.94/1.02  fof(f33,plain,(
% 0.94/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.94/1.02    inference(cnf_transformation,[],[f7])).
% 0.94/1.02  
% 0.94/1.02  fof(f8,axiom,(
% 0.94/1.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.94/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.02  
% 0.94/1.02  fof(f34,plain,(
% 0.94/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.94/1.02    inference(cnf_transformation,[],[f8])).
% 0.94/1.02  
% 0.94/1.02  fof(f9,axiom,(
% 0.94/1.02    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.94/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.02  
% 0.94/1.02  fof(f35,plain,(
% 0.94/1.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.94/1.02    inference(cnf_transformation,[],[f9])).
% 0.94/1.02  
% 0.94/1.02  fof(f10,axiom,(
% 0.94/1.02    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.94/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.02  
% 0.94/1.02  fof(f36,plain,(
% 0.94/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.94/1.02    inference(cnf_transformation,[],[f10])).
% 0.94/1.02  
% 0.94/1.02  fof(f11,axiom,(
% 0.94/1.02    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 0.94/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.02  
% 0.94/1.02  fof(f37,plain,(
% 0.94/1.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 0.94/1.02    inference(cnf_transformation,[],[f11])).
% 0.94/1.02  
% 0.94/1.02  fof(f44,plain,(
% 0.94/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.94/1.02    inference(definition_unfolding,[],[f36,f37])).
% 0.94/1.02  
% 0.94/1.02  fof(f45,plain,(
% 0.94/1.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.94/1.02    inference(definition_unfolding,[],[f35,f44])).
% 0.94/1.02  
% 0.94/1.02  fof(f46,plain,(
% 0.94/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.94/1.02    inference(definition_unfolding,[],[f34,f45])).
% 0.94/1.02  
% 0.94/1.02  fof(f47,plain,(
% 0.94/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.94/1.02    inference(definition_unfolding,[],[f33,f46])).
% 0.94/1.02  
% 0.94/1.02  fof(f48,plain,(
% 0.94/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.94/1.02    inference(definition_unfolding,[],[f32,f47])).
% 0.94/1.02  
% 0.94/1.02  fof(f52,plain,(
% 0.94/1.02    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 0.94/1.02    inference(definition_unfolding,[],[f38,f48])).
% 0.94/1.02  
% 0.94/1.02  fof(f15,axiom,(
% 0.94/1.02    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) = k7_relat_1(X1,X0))),
% 0.94/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.02  
% 0.94/1.02  fof(f21,plain,(
% 0.94/1.02    ! [X0,X1] : (k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.94/1.02    inference(ennf_transformation,[],[f15])).
% 0.94/1.02  
% 0.94/1.02  fof(f42,plain,(
% 0.94/1.02    ( ! [X0,X1] : (k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.94/1.02    inference(cnf_transformation,[],[f21])).
% 0.94/1.02  
% 0.94/1.02  fof(f13,axiom,(
% 0.94/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.94/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.02  
% 0.94/1.02  fof(f39,plain,(
% 0.94/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.94/1.02    inference(cnf_transformation,[],[f13])).
% 0.94/1.02  
% 0.94/1.02  fof(f49,plain,(
% 0.94/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.94/1.02    inference(definition_unfolding,[],[f39,f48])).
% 0.94/1.02  
% 0.94/1.02  fof(f53,plain,(
% 0.94/1.02    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k2_zfmisc_1(X0,k2_relat_1(X1)))) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.94/1.02    inference(definition_unfolding,[],[f42,f49])).
% 0.94/1.02  
% 0.94/1.02  fof(f4,axiom,(
% 0.94/1.02    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.94/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.02  
% 0.94/1.02  fof(f30,plain,(
% 0.94/1.02    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.94/1.02    inference(cnf_transformation,[],[f4])).
% 0.94/1.02  
% 0.94/1.02  fof(f1,axiom,(
% 0.94/1.02    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.94/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.02  
% 0.94/1.02  fof(f27,plain,(
% 0.94/1.02    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.94/1.02    inference(cnf_transformation,[],[f1])).
% 0.94/1.02  
% 0.94/1.02  fof(f3,axiom,(
% 0.94/1.02    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 0.94/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.02  
% 0.94/1.02  fof(f29,plain,(
% 0.94/1.02    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 0.94/1.02    inference(cnf_transformation,[],[f3])).
% 0.94/1.02  
% 0.94/1.02  fof(f2,axiom,(
% 0.94/1.02    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 0.94/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.02  
% 0.94/1.02  fof(f28,plain,(
% 0.94/1.02    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 0.94/1.02    inference(cnf_transformation,[],[f2])).
% 0.94/1.02  
% 0.94/1.02  fof(f50,plain,(
% 0.94/1.02    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k4_xboole_0(X0,X1)) )),
% 0.94/1.02    inference(definition_unfolding,[],[f28,f49])).
% 0.94/1.02  
% 0.94/1.02  fof(f51,plain,(
% 0.94/1.02    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k1_xboole_0) )),
% 0.94/1.02    inference(definition_unfolding,[],[f29,f50])).
% 0.94/1.02  
% 0.94/1.02  fof(f16,conjecture,(
% 0.94/1.02    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.94/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.94/1.02  
% 0.94/1.02  fof(f17,negated_conjecture,(
% 0.94/1.02    ~! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.94/1.02    inference(negated_conjecture,[],[f16])).
% 0.94/1.02  
% 0.94/1.02  fof(f22,plain,(
% 0.94/1.02    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)),
% 0.94/1.02    inference(ennf_transformation,[],[f17])).
% 0.94/1.02  
% 0.94/1.02  fof(f25,plain,(
% 0.94/1.02    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k7_relat_1(k1_xboole_0,sK1)),
% 0.94/1.02    introduced(choice_axiom,[])).
% 0.94/1.02  
% 0.94/1.02  fof(f26,plain,(
% 0.94/1.02    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK1)),
% 0.94/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f25])).
% 0.94/1.02  
% 0.94/1.02  fof(f43,plain,(
% 0.94/1.02    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK1)),
% 0.94/1.02    inference(cnf_transformation,[],[f26])).
% 0.94/1.02  
% 0.94/1.02  cnf(c_6,plain,
% 0.94/1.02      ( r2_hidden(sK0(X0),X0) | v1_relat_1(X0) ),
% 0.94/1.02      inference(cnf_transformation,[],[f40]) ).
% 0.94/1.02  
% 0.94/1.02  cnf(c_3,plain,
% 0.94/1.02      ( r1_xboole_0(X0,k1_xboole_0) ),
% 0.94/1.02      inference(cnf_transformation,[],[f31]) ).
% 0.94/1.02  
% 0.94/1.02  cnf(c_4,plain,
% 0.94/1.02      ( ~ r2_hidden(X0,X1)
% 0.94/1.02      | ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) ),
% 0.94/1.02      inference(cnf_transformation,[],[f52]) ).
% 0.94/1.02  
% 0.94/1.02  cnf(c_76,plain,
% 0.94/1.02      ( ~ r2_hidden(X0,X1)
% 0.94/1.02      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) != X3
% 0.94/1.02      | k1_xboole_0 != X1 ),
% 0.94/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_4]) ).
% 0.94/1.02  
% 0.94/1.02  cnf(c_77,plain,
% 0.94/1.02      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 0.94/1.02      inference(unflattening,[status(thm)],[c_76]) ).
% 0.94/1.02  
% 0.94/1.02  cnf(c_87,plain,
% 0.94/1.02      ( v1_relat_1(X0) | sK0(X0) != X1 | k1_xboole_0 != X0 ),
% 0.94/1.02      inference(resolution_lifted,[status(thm)],[c_6,c_77]) ).
% 0.94/1.02  
% 0.94/1.02  cnf(c_88,plain,
% 0.94/1.02      ( v1_relat_1(k1_xboole_0) ),
% 0.94/1.02      inference(unflattening,[status(thm)],[c_87]) ).
% 0.94/1.02  
% 0.94/1.02  cnf(c_232,plain,
% 0.94/1.02      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 0.94/1.02      inference(predicate_to_equality,[status(thm)],[c_88]) ).
% 0.94/1.02  
% 0.94/1.02  cnf(c_7,plain,
% 0.94/1.02      ( ~ v1_relat_1(X0)
% 0.94/1.02      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(X1,k2_relat_1(X0)))) = k7_relat_1(X0,X1) ),
% 0.94/1.02      inference(cnf_transformation,[],[f53]) ).
% 0.94/1.02  
% 0.94/1.02  cnf(c_233,plain,
% 0.94/1.02      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(X1,k2_relat_1(X0)))) = k7_relat_1(X0,X1)
% 0.94/1.02      | v1_relat_1(X0) != iProver_top ),
% 0.94/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 0.94/1.02  
% 0.94/1.02  cnf(c_444,plain,
% 0.94/1.02      ( k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_zfmisc_1(X0,k2_relat_1(k1_xboole_0)))) = k7_relat_1(k1_xboole_0,X0) ),
% 0.94/1.02      inference(superposition,[status(thm)],[c_232,c_233]) ).
% 0.94/1.02  
% 0.94/1.02  cnf(c_2,plain,
% 0.94/1.02      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 0.94/1.02      inference(cnf_transformation,[],[f30]) ).
% 0.94/1.02  
% 0.94/1.02  cnf(c_0,plain,
% 0.94/1.02      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 0.94/1.02      inference(cnf_transformation,[],[f27]) ).
% 0.94/1.02  
% 0.94/1.02  cnf(c_280,plain,
% 0.94/1.02      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 0.94/1.02      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 0.94/1.02  
% 0.94/1.02  cnf(c_1,plain,
% 0.94/1.02      ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k1_xboole_0 ),
% 0.94/1.02      inference(cnf_transformation,[],[f51]) ).
% 0.94/1.02  
% 0.94/1.02  cnf(c_380,plain,
% 0.94/1.02      ( k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k1_xboole_0 ),
% 0.94/1.02      inference(superposition,[status(thm)],[c_280,c_1]) ).
% 0.94/1.02  
% 0.94/1.02  cnf(c_445,plain,
% 0.94/1.02      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 0.94/1.02      inference(demodulation,[status(thm)],[c_444,c_380]) ).
% 0.94/1.02  
% 0.94/1.02  cnf(c_8,negated_conjecture,
% 0.94/1.02      ( k1_xboole_0 != k7_relat_1(k1_xboole_0,sK1) ),
% 0.94/1.02      inference(cnf_transformation,[],[f43]) ).
% 0.94/1.02  
% 0.94/1.02  cnf(c_448,plain,
% 0.94/1.02      ( k1_xboole_0 != k1_xboole_0 ),
% 0.94/1.02      inference(demodulation,[status(thm)],[c_445,c_8]) ).
% 0.94/1.02  
% 0.94/1.02  cnf(c_158,plain,( X0 = X0 ),theory(equality) ).
% 0.94/1.02  
% 0.94/1.02  cnf(c_172,plain,
% 0.94/1.02      ( k1_xboole_0 = k1_xboole_0 ),
% 0.94/1.02      inference(instantiation,[status(thm)],[c_158]) ).
% 0.94/1.02  
% 0.94/1.02  cnf(contradiction,plain,
% 0.94/1.02      ( $false ),
% 0.94/1.02      inference(minisat,[status(thm)],[c_448,c_172]) ).
% 0.94/1.02  
% 0.94/1.02  
% 0.94/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 0.94/1.02  
% 0.94/1.02  ------                               Statistics
% 0.94/1.02  
% 0.94/1.02  ------ General
% 0.94/1.02  
% 0.94/1.02  abstr_ref_over_cycles:                  0
% 0.94/1.02  abstr_ref_under_cycles:                 0
% 0.94/1.02  gc_basic_clause_elim:                   0
% 0.94/1.02  forced_gc_time:                         0
% 0.94/1.02  parsing_time:                           0.01
% 0.94/1.02  unif_index_cands_time:                  0.
% 0.94/1.02  unif_index_add_time:                    0.
% 0.94/1.02  orderings_time:                         0.
% 0.94/1.02  out_proof_time:                         0.031
% 0.94/1.02  total_time:                             0.075
% 0.94/1.02  num_of_symbols:                         44
% 0.94/1.02  num_of_terms:                           546
% 0.94/1.02  
% 0.94/1.02  ------ Preprocessing
% 0.94/1.02  
% 0.94/1.02  num_of_splits:                          0
% 0.94/1.02  num_of_split_atoms:                     0
% 0.94/1.02  num_of_reused_defs:                     0
% 0.94/1.02  num_eq_ax_congr_red:                    17
% 0.94/1.02  num_of_sem_filtered_clauses:            1
% 0.94/1.02  num_of_subtypes:                        0
% 0.94/1.02  monotx_restored_types:                  0
% 0.94/1.02  sat_num_of_epr_types:                   0
% 0.94/1.02  sat_num_of_non_cyclic_types:            0
% 0.94/1.02  sat_guarded_non_collapsed_types:        0
% 0.94/1.02  num_pure_diseq_elim:                    0
% 0.94/1.02  simp_replaced_by:                       0
% 0.94/1.02  res_preprocessed:                       47
% 0.94/1.02  prep_upred:                             0
% 0.94/1.02  prep_unflattend:                        6
% 0.94/1.02  smt_new_axioms:                         0
% 0.94/1.02  pred_elim_cands:                        1
% 0.94/1.02  pred_elim:                              2
% 0.94/1.02  pred_elim_cl:                           2
% 0.94/1.02  pred_elim_cycles:                       4
% 0.94/1.02  merged_defs:                            0
% 0.94/1.02  merged_defs_ncl:                        0
% 0.94/1.02  bin_hyper_res:                          0
% 0.94/1.02  prep_cycles:                            4
% 0.94/1.02  pred_elim_time:                         0.001
% 0.94/1.02  splitting_time:                         0.
% 0.94/1.02  sem_filter_time:                        0.
% 0.94/1.02  monotx_time:                            0.
% 0.94/1.02  subtype_inf_time:                       0.
% 0.94/1.02  
% 0.94/1.02  ------ Problem properties
% 0.94/1.02  
% 0.94/1.02  clauses:                                7
% 0.94/1.02  conjectures:                            1
% 0.94/1.02  epr:                                    1
% 0.94/1.02  horn:                                   7
% 0.94/1.02  ground:                                 2
% 0.94/1.02  unary:                                  5
% 0.94/1.02  binary:                                 2
% 0.94/1.02  lits:                                   9
% 0.94/1.02  lits_eq:                                6
% 0.94/1.02  fd_pure:                                0
% 0.94/1.02  fd_pseudo:                              0
% 0.94/1.02  fd_cond:                                0
% 0.94/1.02  fd_pseudo_cond:                         0
% 0.94/1.02  ac_symbols:                             0
% 0.94/1.02  
% 0.94/1.02  ------ Propositional Solver
% 0.94/1.02  
% 0.94/1.02  prop_solver_calls:                      27
% 0.94/1.02  prop_fast_solver_calls:                 206
% 0.94/1.02  smt_solver_calls:                       0
% 0.94/1.02  smt_fast_solver_calls:                  0
% 0.94/1.02  prop_num_of_clauses:                    153
% 0.94/1.02  prop_preprocess_simplified:             1125
% 0.94/1.02  prop_fo_subsumed:                       0
% 0.94/1.02  prop_solver_time:                       0.
% 0.94/1.02  smt_solver_time:                        0.
% 0.94/1.02  smt_fast_solver_time:                   0.
% 0.94/1.02  prop_fast_solver_time:                  0.
% 0.94/1.02  prop_unsat_core_time:                   0.
% 0.94/1.02  
% 0.94/1.02  ------ QBF
% 0.94/1.02  
% 0.94/1.02  qbf_q_res:                              0
% 0.94/1.02  qbf_num_tautologies:                    0
% 0.94/1.02  qbf_prep_cycles:                        0
% 0.94/1.02  
% 0.94/1.02  ------ BMC1
% 0.94/1.02  
% 0.94/1.02  bmc1_current_bound:                     -1
% 0.94/1.02  bmc1_last_solved_bound:                 -1
% 0.94/1.02  bmc1_unsat_core_size:                   -1
% 0.94/1.02  bmc1_unsat_core_parents_size:           -1
% 0.94/1.02  bmc1_merge_next_fun:                    0
% 0.94/1.02  bmc1_unsat_core_clauses_time:           0.
% 0.94/1.02  
% 0.94/1.02  ------ Instantiation
% 0.94/1.02  
% 0.94/1.02  inst_num_of_clauses:                    85
% 0.94/1.02  inst_num_in_passive:                    22
% 0.94/1.02  inst_num_in_active:                     46
% 0.94/1.02  inst_num_in_unprocessed:                17
% 0.94/1.02  inst_num_of_loops:                      50
% 0.94/1.02  inst_num_of_learning_restarts:          0
% 0.94/1.02  inst_num_moves_active_passive:          0
% 0.94/1.02  inst_lit_activity:                      0
% 0.94/1.02  inst_lit_activity_moves:                0
% 0.94/1.02  inst_num_tautologies:                   0
% 0.94/1.02  inst_num_prop_implied:                  0
% 0.94/1.02  inst_num_existing_simplified:           0
% 0.94/1.02  inst_num_eq_res_simplified:             0
% 0.94/1.02  inst_num_child_elim:                    0
% 0.94/1.02  inst_num_of_dismatching_blockings:      3
% 0.94/1.02  inst_num_of_non_proper_insts:           49
% 0.94/1.02  inst_num_of_duplicates:                 0
% 0.94/1.02  inst_inst_num_from_inst_to_res:         0
% 0.94/1.02  inst_dismatching_checking_time:         0.
% 0.94/1.02  
% 0.94/1.02  ------ Resolution
% 0.94/1.02  
% 0.94/1.02  res_num_of_clauses:                     0
% 0.94/1.02  res_num_in_passive:                     0
% 0.94/1.02  res_num_in_active:                      0
% 0.94/1.02  res_num_of_loops:                       51
% 0.94/1.02  res_forward_subset_subsumed:            19
% 0.94/1.02  res_backward_subset_subsumed:           0
% 0.94/1.02  res_forward_subsumed:                   0
% 0.94/1.02  res_backward_subsumed:                  0
% 0.94/1.02  res_forward_subsumption_resolution:     0
% 0.94/1.02  res_backward_subsumption_resolution:    0
% 0.94/1.02  res_clause_to_clause_subsumption:       13
% 0.94/1.02  res_orphan_elimination:                 0
% 0.94/1.02  res_tautology_del:                      8
% 0.94/1.02  res_num_eq_res_simplified:              0
% 0.94/1.02  res_num_sel_changes:                    0
% 0.94/1.02  res_moves_from_active_to_pass:          0
% 0.94/1.02  
% 0.94/1.02  ------ Superposition
% 0.94/1.02  
% 0.94/1.02  sup_time_total:                         0.
% 0.94/1.02  sup_time_generating:                    0.
% 0.94/1.02  sup_time_sim_full:                      0.
% 0.94/1.02  sup_time_sim_immed:                     0.
% 0.94/1.02  
% 0.94/1.02  sup_num_of_clauses:                     9
% 0.94/1.02  sup_num_in_active:                      7
% 0.94/1.02  sup_num_in_passive:                     2
% 0.94/1.02  sup_num_of_loops:                       9
% 0.94/1.02  sup_fw_superposition:                   6
% 0.94/1.02  sup_bw_superposition:                   5
% 0.94/1.02  sup_immediate_simplified:               2
% 0.94/1.02  sup_given_eliminated:                   0
% 0.94/1.02  comparisons_done:                       0
% 0.94/1.02  comparisons_avoided:                    0
% 0.94/1.02  
% 0.94/1.02  ------ Simplifications
% 0.94/1.02  
% 0.94/1.02  
% 0.94/1.02  sim_fw_subset_subsumed:                 0
% 0.94/1.02  sim_bw_subset_subsumed:                 0
% 0.94/1.02  sim_fw_subsumed:                        1
% 0.94/1.02  sim_bw_subsumed:                        0
% 0.94/1.02  sim_fw_subsumption_res:                 0
% 0.94/1.02  sim_bw_subsumption_res:                 0
% 0.94/1.02  sim_tautology_del:                      0
% 0.94/1.02  sim_eq_tautology_del:                   0
% 0.94/1.02  sim_eq_res_simp:                        0
% 0.94/1.02  sim_fw_demodulated:                     1
% 0.94/1.02  sim_bw_demodulated:                     2
% 0.94/1.02  sim_light_normalised:                   0
% 0.94/1.02  sim_joinable_taut:                      0
% 0.94/1.02  sim_joinable_simp:                      0
% 0.94/1.02  sim_ac_normalised:                      0
% 0.94/1.02  sim_smt_subsumption:                    0
% 0.94/1.02  
%------------------------------------------------------------------------------
