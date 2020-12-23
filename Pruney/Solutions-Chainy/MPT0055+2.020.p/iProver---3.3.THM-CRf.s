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
% DateTime   : Thu Dec  3 11:22:52 EST 2020

% Result     : Theorem 12.04s
% Output     : CNFRefutation 12.04s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 219 expanded)
%              Number of clauses        :   52 ( 108 expanded)
%              Number of leaves         :   11 (  54 expanded)
%              Depth                    :   20
%              Number of atoms          :   87 ( 229 expanded)
%              Number of equality atoms :   79 ( 221 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f10,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f10])).

fof(f13,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f11])).

fof(f14,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f25,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_303,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X1,X0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_8])).

cnf(c_5,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_7,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_250,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_7])).

cnf(c_629,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_5,c_250])).

cnf(c_637,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_629,c_250])).

cnf(c_1173,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k4_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_303,c_637])).

cnf(c_1188,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1173,c_303])).

cnf(c_2,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_45,plain,
    ( k4_xboole_0(X0,X1) != X2
    | k3_xboole_0(X2,X3) != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_4])).

cnf(c_46,plain,
    ( k3_xboole_0(k4_xboole_0(X0,X1),X2) != X1
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_45])).

cnf(c_306,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | k3_xboole_0(k4_xboole_0(X0,X1),X2) != k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_8,c_46])).

cnf(c_1544,plain,
    ( k3_xboole_0(k4_xboole_0(X0,X1),X1) != k3_xboole_0(k4_xboole_0(X0,X1),X2)
    | k3_xboole_0(k4_xboole_0(X0,X1),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_637,c_306])).

cnf(c_57799,plain,
    ( k3_xboole_0(k4_xboole_0(X0,X1),X1) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_1544])).

cnf(c_60506,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_57799,c_303])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_60518,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_60506,c_6])).

cnf(c_252,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_5,c_7])).

cnf(c_61180,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_60518,c_252])).

cnf(c_63367,plain,
    ( k4_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1188,c_61180])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_632,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_250,c_5])).

cnf(c_635,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_632,c_5])).

cnf(c_253,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_7,c_5])).

cnf(c_256,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_253,c_5])).

cnf(c_930,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_635,c_256])).

cnf(c_254,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7,c_6])).

cnf(c_255,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_254,c_6])).

cnf(c_364,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_255])).

cnf(c_374,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_364,c_7])).

cnf(c_377,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_364,c_3])).

cnf(c_454,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_377,c_8])).

cnf(c_459,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_454,c_6])).

cnf(c_512,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_374,c_459])).

cnf(c_514,plain,
    ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_512,c_5])).

cnf(c_516,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_514,c_255])).

cnf(c_931,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_930,c_516])).

cnf(c_1195,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_931])).

cnf(c_1568,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3,c_1195])).

cnf(c_1600,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1568,c_3])).

cnf(c_305,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_8,c_5])).

cnf(c_1681,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_1600,c_305])).

cnf(c_2339,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_1681])).

cnf(c_63592,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_63367,c_2339])).

cnf(c_9,negated_conjecture,
    ( k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_65120,plain,
    ( k3_xboole_0(sK1,sK0) != k3_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_63592,c_9])).

cnf(c_155,plain,
    ( k3_xboole_0(sK1,sK0) = k3_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_65120,c_155])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.31  % Computer   : n004.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 18:57:08 EST 2020
% 0.15/0.31  % CPUTime    : 
% 0.15/0.31  % Running in FOF mode
% 12.04/1.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.04/1.96  
% 12.04/1.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 12.04/1.96  
% 12.04/1.96  ------  iProver source info
% 12.04/1.96  
% 12.04/1.96  git: date: 2020-06-30 10:37:57 +0100
% 12.04/1.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 12.04/1.96  git: non_committed_changes: false
% 12.04/1.96  git: last_make_outside_of_git: false
% 12.04/1.96  
% 12.04/1.96  ------ 
% 12.04/1.96  
% 12.04/1.96  ------ Input Options
% 12.04/1.96  
% 12.04/1.96  --out_options                           all
% 12.04/1.96  --tptp_safe_out                         true
% 12.04/1.96  --problem_path                          ""
% 12.04/1.96  --include_path                          ""
% 12.04/1.96  --clausifier                            res/vclausify_rel
% 12.04/1.96  --clausifier_options                    ""
% 12.04/1.96  --stdin                                 false
% 12.04/1.96  --stats_out                             all
% 12.04/1.96  
% 12.04/1.96  ------ General Options
% 12.04/1.96  
% 12.04/1.96  --fof                                   false
% 12.04/1.96  --time_out_real                         305.
% 12.04/1.96  --time_out_virtual                      -1.
% 12.04/1.96  --symbol_type_check                     false
% 12.04/1.96  --clausify_out                          false
% 12.04/1.96  --sig_cnt_out                           false
% 12.04/1.96  --trig_cnt_out                          false
% 12.04/1.96  --trig_cnt_out_tolerance                1.
% 12.04/1.96  --trig_cnt_out_sk_spl                   false
% 12.04/1.96  --abstr_cl_out                          false
% 12.04/1.96  
% 12.04/1.96  ------ Global Options
% 12.04/1.96  
% 12.04/1.96  --schedule                              default
% 12.04/1.96  --add_important_lit                     false
% 12.04/1.96  --prop_solver_per_cl                    1000
% 12.04/1.96  --min_unsat_core                        false
% 12.04/1.96  --soft_assumptions                      false
% 12.04/1.96  --soft_lemma_size                       3
% 12.04/1.96  --prop_impl_unit_size                   0
% 12.04/1.96  --prop_impl_unit                        []
% 12.04/1.96  --share_sel_clauses                     true
% 12.04/1.96  --reset_solvers                         false
% 12.04/1.96  --bc_imp_inh                            [conj_cone]
% 12.04/1.96  --conj_cone_tolerance                   3.
% 12.04/1.96  --extra_neg_conj                        none
% 12.04/1.96  --large_theory_mode                     true
% 12.04/1.96  --prolific_symb_bound                   200
% 12.04/1.96  --lt_threshold                          2000
% 12.04/1.96  --clause_weak_htbl                      true
% 12.04/1.96  --gc_record_bc_elim                     false
% 12.04/1.96  
% 12.04/1.96  ------ Preprocessing Options
% 12.04/1.96  
% 12.04/1.96  --preprocessing_flag                    true
% 12.04/1.96  --time_out_prep_mult                    0.1
% 12.04/1.96  --splitting_mode                        input
% 12.04/1.96  --splitting_grd                         true
% 12.04/1.96  --splitting_cvd                         false
% 12.04/1.96  --splitting_cvd_svl                     false
% 12.04/1.96  --splitting_nvd                         32
% 12.04/1.96  --sub_typing                            true
% 12.04/1.96  --prep_gs_sim                           true
% 12.04/1.96  --prep_unflatten                        true
% 12.04/1.96  --prep_res_sim                          true
% 12.04/1.96  --prep_upred                            true
% 12.04/1.96  --prep_sem_filter                       exhaustive
% 12.04/1.96  --prep_sem_filter_out                   false
% 12.04/1.96  --pred_elim                             true
% 12.04/1.96  --res_sim_input                         true
% 12.04/1.96  --eq_ax_congr_red                       true
% 12.04/1.96  --pure_diseq_elim                       true
% 12.04/1.96  --brand_transform                       false
% 12.04/1.96  --non_eq_to_eq                          false
% 12.04/1.96  --prep_def_merge                        true
% 12.04/1.96  --prep_def_merge_prop_impl              false
% 12.04/1.96  --prep_def_merge_mbd                    true
% 12.04/1.96  --prep_def_merge_tr_red                 false
% 12.04/1.96  --prep_def_merge_tr_cl                  false
% 12.04/1.96  --smt_preprocessing                     true
% 12.04/1.96  --smt_ac_axioms                         fast
% 12.04/1.96  --preprocessed_out                      false
% 12.04/1.96  --preprocessed_stats                    false
% 12.04/1.96  
% 12.04/1.96  ------ Abstraction refinement Options
% 12.04/1.96  
% 12.04/1.96  --abstr_ref                             []
% 12.04/1.96  --abstr_ref_prep                        false
% 12.04/1.96  --abstr_ref_until_sat                   false
% 12.04/1.96  --abstr_ref_sig_restrict                funpre
% 12.04/1.96  --abstr_ref_af_restrict_to_split_sk     false
% 12.04/1.96  --abstr_ref_under                       []
% 12.04/1.96  
% 12.04/1.96  ------ SAT Options
% 12.04/1.96  
% 12.04/1.96  --sat_mode                              false
% 12.04/1.96  --sat_fm_restart_options                ""
% 12.04/1.96  --sat_gr_def                            false
% 12.04/1.96  --sat_epr_types                         true
% 12.04/1.96  --sat_non_cyclic_types                  false
% 12.04/1.96  --sat_finite_models                     false
% 12.04/1.96  --sat_fm_lemmas                         false
% 12.04/1.96  --sat_fm_prep                           false
% 12.04/1.96  --sat_fm_uc_incr                        true
% 12.04/1.96  --sat_out_model                         small
% 12.04/1.96  --sat_out_clauses                       false
% 12.04/1.96  
% 12.04/1.96  ------ QBF Options
% 12.04/1.96  
% 12.04/1.96  --qbf_mode                              false
% 12.04/1.96  --qbf_elim_univ                         false
% 12.04/1.96  --qbf_dom_inst                          none
% 12.04/1.96  --qbf_dom_pre_inst                      false
% 12.04/1.96  --qbf_sk_in                             false
% 12.04/1.96  --qbf_pred_elim                         true
% 12.04/1.96  --qbf_split                             512
% 12.04/1.96  
% 12.04/1.96  ------ BMC1 Options
% 12.04/1.96  
% 12.04/1.96  --bmc1_incremental                      false
% 12.04/1.96  --bmc1_axioms                           reachable_all
% 12.04/1.96  --bmc1_min_bound                        0
% 12.04/1.96  --bmc1_max_bound                        -1
% 12.04/1.96  --bmc1_max_bound_default                -1
% 12.04/1.96  --bmc1_symbol_reachability              true
% 12.04/1.96  --bmc1_property_lemmas                  false
% 12.04/1.96  --bmc1_k_induction                      false
% 12.04/1.96  --bmc1_non_equiv_states                 false
% 12.04/1.96  --bmc1_deadlock                         false
% 12.04/1.96  --bmc1_ucm                              false
% 12.04/1.96  --bmc1_add_unsat_core                   none
% 12.04/1.96  --bmc1_unsat_core_children              false
% 12.04/1.96  --bmc1_unsat_core_extrapolate_axioms    false
% 12.04/1.96  --bmc1_out_stat                         full
% 12.04/1.96  --bmc1_ground_init                      false
% 12.04/1.96  --bmc1_pre_inst_next_state              false
% 12.04/1.96  --bmc1_pre_inst_state                   false
% 12.04/1.96  --bmc1_pre_inst_reach_state             false
% 12.04/1.96  --bmc1_out_unsat_core                   false
% 12.04/1.96  --bmc1_aig_witness_out                  false
% 12.04/1.96  --bmc1_verbose                          false
% 12.04/1.96  --bmc1_dump_clauses_tptp                false
% 12.04/1.96  --bmc1_dump_unsat_core_tptp             false
% 12.04/1.96  --bmc1_dump_file                        -
% 12.04/1.96  --bmc1_ucm_expand_uc_limit              128
% 12.04/1.96  --bmc1_ucm_n_expand_iterations          6
% 12.04/1.96  --bmc1_ucm_extend_mode                  1
% 12.04/1.96  --bmc1_ucm_init_mode                    2
% 12.04/1.96  --bmc1_ucm_cone_mode                    none
% 12.04/1.96  --bmc1_ucm_reduced_relation_type        0
% 12.04/1.96  --bmc1_ucm_relax_model                  4
% 12.04/1.96  --bmc1_ucm_full_tr_after_sat            true
% 12.04/1.96  --bmc1_ucm_expand_neg_assumptions       false
% 12.04/1.96  --bmc1_ucm_layered_model                none
% 12.04/1.96  --bmc1_ucm_max_lemma_size               10
% 12.04/1.96  
% 12.04/1.96  ------ AIG Options
% 12.04/1.96  
% 12.04/1.96  --aig_mode                              false
% 12.04/1.96  
% 12.04/1.96  ------ Instantiation Options
% 12.04/1.96  
% 12.04/1.96  --instantiation_flag                    true
% 12.04/1.96  --inst_sos_flag                         true
% 12.04/1.96  --inst_sos_phase                        true
% 12.04/1.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.04/1.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.04/1.96  --inst_lit_sel_side                     num_symb
% 12.04/1.96  --inst_solver_per_active                1400
% 12.04/1.96  --inst_solver_calls_frac                1.
% 12.04/1.96  --inst_passive_queue_type               priority_queues
% 12.04/1.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.04/1.96  --inst_passive_queues_freq              [25;2]
% 12.04/1.96  --inst_dismatching                      true
% 12.04/1.96  --inst_eager_unprocessed_to_passive     true
% 12.04/1.96  --inst_prop_sim_given                   true
% 12.04/1.96  --inst_prop_sim_new                     false
% 12.04/1.96  --inst_subs_new                         false
% 12.04/1.96  --inst_eq_res_simp                      false
% 12.04/1.96  --inst_subs_given                       false
% 12.04/1.96  --inst_orphan_elimination               true
% 12.04/1.96  --inst_learning_loop_flag               true
% 12.04/1.96  --inst_learning_start                   3000
% 12.04/1.96  --inst_learning_factor                  2
% 12.04/1.96  --inst_start_prop_sim_after_learn       3
% 12.04/1.96  --inst_sel_renew                        solver
% 12.04/1.96  --inst_lit_activity_flag                true
% 12.04/1.96  --inst_restr_to_given                   false
% 12.04/1.96  --inst_activity_threshold               500
% 12.04/1.96  --inst_out_proof                        true
% 12.04/1.96  
% 12.04/1.96  ------ Resolution Options
% 12.04/1.96  
% 12.04/1.96  --resolution_flag                       true
% 12.04/1.96  --res_lit_sel                           adaptive
% 12.04/1.96  --res_lit_sel_side                      none
% 12.04/1.96  --res_ordering                          kbo
% 12.04/1.96  --res_to_prop_solver                    active
% 12.04/1.96  --res_prop_simpl_new                    false
% 12.04/1.96  --res_prop_simpl_given                  true
% 12.04/1.96  --res_passive_queue_type                priority_queues
% 12.04/1.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.04/1.96  --res_passive_queues_freq               [15;5]
% 12.04/1.96  --res_forward_subs                      full
% 12.04/1.96  --res_backward_subs                     full
% 12.04/1.96  --res_forward_subs_resolution           true
% 12.04/1.96  --res_backward_subs_resolution          true
% 12.04/1.96  --res_orphan_elimination                true
% 12.04/1.96  --res_time_limit                        2.
% 12.04/1.96  --res_out_proof                         true
% 12.04/1.96  
% 12.04/1.96  ------ Superposition Options
% 12.04/1.96  
% 12.04/1.96  --superposition_flag                    true
% 12.04/1.96  --sup_passive_queue_type                priority_queues
% 12.04/1.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.04/1.96  --sup_passive_queues_freq               [8;1;4]
% 12.04/1.96  --demod_completeness_check              fast
% 12.04/1.96  --demod_use_ground                      true
% 12.04/1.96  --sup_to_prop_solver                    passive
% 12.04/1.96  --sup_prop_simpl_new                    true
% 12.04/1.96  --sup_prop_simpl_given                  true
% 12.04/1.96  --sup_fun_splitting                     true
% 12.04/1.96  --sup_smt_interval                      50000
% 12.04/1.96  
% 12.04/1.96  ------ Superposition Simplification Setup
% 12.04/1.96  
% 12.04/1.96  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 12.04/1.96  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 12.04/1.96  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 12.04/1.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 12.04/1.96  --sup_full_triv                         [TrivRules;PropSubs]
% 12.04/1.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 12.04/1.96  --sup_full_bw                           [BwDemod;BwSubsumption]
% 12.04/1.96  --sup_immed_triv                        [TrivRules]
% 12.04/1.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.04/1.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.04/1.96  --sup_immed_bw_main                     []
% 12.04/1.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 12.04/1.96  --sup_input_triv                        [Unflattening;TrivRules]
% 12.04/1.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.04/1.96  --sup_input_bw                          []
% 12.04/1.96  
% 12.04/1.96  ------ Combination Options
% 12.04/1.96  
% 12.04/1.96  --comb_res_mult                         3
% 12.04/1.96  --comb_sup_mult                         2
% 12.04/1.96  --comb_inst_mult                        10
% 12.04/1.96  
% 12.04/1.96  ------ Debug Options
% 12.04/1.96  
% 12.04/1.96  --dbg_backtrace                         false
% 12.04/1.96  --dbg_dump_prop_clauses                 false
% 12.04/1.96  --dbg_dump_prop_clauses_file            -
% 12.04/1.96  --dbg_out_stat                          false
% 12.04/1.96  ------ Parsing...
% 12.04/1.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 12.04/1.96  
% 12.04/1.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 12.04/1.96  
% 12.04/1.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 12.04/1.96  
% 12.04/1.96  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 12.04/1.96  ------ Proving...
% 12.04/1.96  ------ Problem Properties 
% 12.04/1.96  
% 12.04/1.96  
% 12.04/1.96  clauses                                 9
% 12.04/1.96  conjectures                             1
% 12.04/1.96  EPR                                     0
% 12.04/1.96  Horn                                    9
% 12.04/1.96  unary                                   8
% 12.04/1.96  binary                                  1
% 12.04/1.96  lits                                    10
% 12.04/1.96  lits eq                                 10
% 12.04/1.96  fd_pure                                 0
% 12.04/1.96  fd_pseudo                               0
% 12.04/1.96  fd_cond                                 1
% 12.04/1.96  fd_pseudo_cond                          0
% 12.04/1.96  AC symbols                              0
% 12.04/1.96  
% 12.04/1.96  ------ Schedule dynamic 5 is on 
% 12.04/1.96  
% 12.04/1.96  ------ pure equality problem: resolution off 
% 12.04/1.96  
% 12.04/1.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 12.04/1.96  
% 12.04/1.96  
% 12.04/1.96  ------ 
% 12.04/1.96  Current options:
% 12.04/1.96  ------ 
% 12.04/1.96  
% 12.04/1.96  ------ Input Options
% 12.04/1.96  
% 12.04/1.96  --out_options                           all
% 12.04/1.96  --tptp_safe_out                         true
% 12.04/1.96  --problem_path                          ""
% 12.04/1.96  --include_path                          ""
% 12.04/1.96  --clausifier                            res/vclausify_rel
% 12.04/1.96  --clausifier_options                    ""
% 12.04/1.96  --stdin                                 false
% 12.04/1.96  --stats_out                             all
% 12.04/1.96  
% 12.04/1.96  ------ General Options
% 12.04/1.96  
% 12.04/1.96  --fof                                   false
% 12.04/1.96  --time_out_real                         305.
% 12.04/1.96  --time_out_virtual                      -1.
% 12.04/1.96  --symbol_type_check                     false
% 12.04/1.96  --clausify_out                          false
% 12.04/1.96  --sig_cnt_out                           false
% 12.04/1.96  --trig_cnt_out                          false
% 12.04/1.96  --trig_cnt_out_tolerance                1.
% 12.04/1.96  --trig_cnt_out_sk_spl                   false
% 12.04/1.96  --abstr_cl_out                          false
% 12.04/1.96  
% 12.04/1.96  ------ Global Options
% 12.04/1.96  
% 12.04/1.96  --schedule                              default
% 12.04/1.96  --add_important_lit                     false
% 12.04/1.96  --prop_solver_per_cl                    1000
% 12.04/1.96  --min_unsat_core                        false
% 12.04/1.96  --soft_assumptions                      false
% 12.04/1.96  --soft_lemma_size                       3
% 12.04/1.96  --prop_impl_unit_size                   0
% 12.04/1.96  --prop_impl_unit                        []
% 12.04/1.96  --share_sel_clauses                     true
% 12.04/1.96  --reset_solvers                         false
% 12.04/1.96  --bc_imp_inh                            [conj_cone]
% 12.04/1.96  --conj_cone_tolerance                   3.
% 12.04/1.96  --extra_neg_conj                        none
% 12.04/1.96  --large_theory_mode                     true
% 12.04/1.96  --prolific_symb_bound                   200
% 12.04/1.96  --lt_threshold                          2000
% 12.04/1.96  --clause_weak_htbl                      true
% 12.04/1.96  --gc_record_bc_elim                     false
% 12.04/1.96  
% 12.04/1.96  ------ Preprocessing Options
% 12.04/1.96  
% 12.04/1.96  --preprocessing_flag                    true
% 12.04/1.96  --time_out_prep_mult                    0.1
% 12.04/1.96  --splitting_mode                        input
% 12.04/1.96  --splitting_grd                         true
% 12.04/1.96  --splitting_cvd                         false
% 12.04/1.96  --splitting_cvd_svl                     false
% 12.04/1.96  --splitting_nvd                         32
% 12.04/1.96  --sub_typing                            true
% 12.04/1.96  --prep_gs_sim                           true
% 12.04/1.96  --prep_unflatten                        true
% 12.04/1.96  --prep_res_sim                          true
% 12.04/1.96  --prep_upred                            true
% 12.04/1.96  --prep_sem_filter                       exhaustive
% 12.04/1.96  --prep_sem_filter_out                   false
% 12.04/1.96  --pred_elim                             true
% 12.04/1.96  --res_sim_input                         true
% 12.04/1.96  --eq_ax_congr_red                       true
% 12.04/1.96  --pure_diseq_elim                       true
% 12.04/1.96  --brand_transform                       false
% 12.04/1.96  --non_eq_to_eq                          false
% 12.04/1.96  --prep_def_merge                        true
% 12.04/1.96  --prep_def_merge_prop_impl              false
% 12.04/1.96  --prep_def_merge_mbd                    true
% 12.04/1.96  --prep_def_merge_tr_red                 false
% 12.04/1.96  --prep_def_merge_tr_cl                  false
% 12.04/1.96  --smt_preprocessing                     true
% 12.04/1.96  --smt_ac_axioms                         fast
% 12.04/1.96  --preprocessed_out                      false
% 12.04/1.96  --preprocessed_stats                    false
% 12.04/1.96  
% 12.04/1.96  ------ Abstraction refinement Options
% 12.04/1.96  
% 12.04/1.96  --abstr_ref                             []
% 12.04/1.96  --abstr_ref_prep                        false
% 12.04/1.96  --abstr_ref_until_sat                   false
% 12.04/1.96  --abstr_ref_sig_restrict                funpre
% 12.04/1.96  --abstr_ref_af_restrict_to_split_sk     false
% 12.04/1.96  --abstr_ref_under                       []
% 12.04/1.96  
% 12.04/1.96  ------ SAT Options
% 12.04/1.96  
% 12.04/1.96  --sat_mode                              false
% 12.04/1.96  --sat_fm_restart_options                ""
% 12.04/1.96  --sat_gr_def                            false
% 12.04/1.96  --sat_epr_types                         true
% 12.04/1.96  --sat_non_cyclic_types                  false
% 12.04/1.96  --sat_finite_models                     false
% 12.04/1.96  --sat_fm_lemmas                         false
% 12.04/1.96  --sat_fm_prep                           false
% 12.04/1.96  --sat_fm_uc_incr                        true
% 12.04/1.96  --sat_out_model                         small
% 12.04/1.96  --sat_out_clauses                       false
% 12.04/1.96  
% 12.04/1.96  ------ QBF Options
% 12.04/1.96  
% 12.04/1.96  --qbf_mode                              false
% 12.04/1.96  --qbf_elim_univ                         false
% 12.04/1.96  --qbf_dom_inst                          none
% 12.04/1.96  --qbf_dom_pre_inst                      false
% 12.04/1.96  --qbf_sk_in                             false
% 12.04/1.96  --qbf_pred_elim                         true
% 12.04/1.96  --qbf_split                             512
% 12.04/1.96  
% 12.04/1.96  ------ BMC1 Options
% 12.04/1.96  
% 12.04/1.96  --bmc1_incremental                      false
% 12.04/1.96  --bmc1_axioms                           reachable_all
% 12.04/1.96  --bmc1_min_bound                        0
% 12.04/1.96  --bmc1_max_bound                        -1
% 12.04/1.96  --bmc1_max_bound_default                -1
% 12.04/1.96  --bmc1_symbol_reachability              true
% 12.04/1.96  --bmc1_property_lemmas                  false
% 12.04/1.96  --bmc1_k_induction                      false
% 12.04/1.96  --bmc1_non_equiv_states                 false
% 12.04/1.96  --bmc1_deadlock                         false
% 12.04/1.96  --bmc1_ucm                              false
% 12.04/1.96  --bmc1_add_unsat_core                   none
% 12.04/1.96  --bmc1_unsat_core_children              false
% 12.04/1.96  --bmc1_unsat_core_extrapolate_axioms    false
% 12.04/1.96  --bmc1_out_stat                         full
% 12.04/1.96  --bmc1_ground_init                      false
% 12.04/1.96  --bmc1_pre_inst_next_state              false
% 12.04/1.96  --bmc1_pre_inst_state                   false
% 12.04/1.96  --bmc1_pre_inst_reach_state             false
% 12.04/1.96  --bmc1_out_unsat_core                   false
% 12.04/1.96  --bmc1_aig_witness_out                  false
% 12.04/1.96  --bmc1_verbose                          false
% 12.04/1.96  --bmc1_dump_clauses_tptp                false
% 12.04/1.96  --bmc1_dump_unsat_core_tptp             false
% 12.04/1.96  --bmc1_dump_file                        -
% 12.04/1.96  --bmc1_ucm_expand_uc_limit              128
% 12.04/1.96  --bmc1_ucm_n_expand_iterations          6
% 12.04/1.96  --bmc1_ucm_extend_mode                  1
% 12.04/1.96  --bmc1_ucm_init_mode                    2
% 12.04/1.96  --bmc1_ucm_cone_mode                    none
% 12.04/1.96  --bmc1_ucm_reduced_relation_type        0
% 12.04/1.96  --bmc1_ucm_relax_model                  4
% 12.04/1.96  --bmc1_ucm_full_tr_after_sat            true
% 12.04/1.96  --bmc1_ucm_expand_neg_assumptions       false
% 12.04/1.96  --bmc1_ucm_layered_model                none
% 12.04/1.96  --bmc1_ucm_max_lemma_size               10
% 12.04/1.96  
% 12.04/1.96  ------ AIG Options
% 12.04/1.96  
% 12.04/1.96  --aig_mode                              false
% 12.04/1.96  
% 12.04/1.96  ------ Instantiation Options
% 12.04/1.96  
% 12.04/1.96  --instantiation_flag                    true
% 12.04/1.96  --inst_sos_flag                         true
% 12.04/1.96  --inst_sos_phase                        true
% 12.04/1.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.04/1.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.04/1.96  --inst_lit_sel_side                     none
% 12.04/1.96  --inst_solver_per_active                1400
% 12.04/1.96  --inst_solver_calls_frac                1.
% 12.04/1.96  --inst_passive_queue_type               priority_queues
% 12.04/1.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.04/1.96  --inst_passive_queues_freq              [25;2]
% 12.04/1.96  --inst_dismatching                      true
% 12.04/1.96  --inst_eager_unprocessed_to_passive     true
% 12.04/1.96  --inst_prop_sim_given                   true
% 12.04/1.96  --inst_prop_sim_new                     false
% 12.04/1.96  --inst_subs_new                         false
% 12.04/1.96  --inst_eq_res_simp                      false
% 12.04/1.96  --inst_subs_given                       false
% 12.04/1.96  --inst_orphan_elimination               true
% 12.04/1.96  --inst_learning_loop_flag               true
% 12.04/1.96  --inst_learning_start                   3000
% 12.04/1.96  --inst_learning_factor                  2
% 12.04/1.96  --inst_start_prop_sim_after_learn       3
% 12.04/1.96  --inst_sel_renew                        solver
% 12.04/1.96  --inst_lit_activity_flag                true
% 12.04/1.96  --inst_restr_to_given                   false
% 12.04/1.96  --inst_activity_threshold               500
% 12.04/1.96  --inst_out_proof                        true
% 12.04/1.96  
% 12.04/1.96  ------ Resolution Options
% 12.04/1.96  
% 12.04/1.96  --resolution_flag                       false
% 12.04/1.96  --res_lit_sel                           adaptive
% 12.04/1.96  --res_lit_sel_side                      none
% 12.04/1.96  --res_ordering                          kbo
% 12.04/1.96  --res_to_prop_solver                    active
% 12.04/1.96  --res_prop_simpl_new                    false
% 12.04/1.96  --res_prop_simpl_given                  true
% 12.04/1.96  --res_passive_queue_type                priority_queues
% 12.04/1.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.04/1.96  --res_passive_queues_freq               [15;5]
% 12.04/1.96  --res_forward_subs                      full
% 12.04/1.96  --res_backward_subs                     full
% 12.04/1.96  --res_forward_subs_resolution           true
% 12.04/1.96  --res_backward_subs_resolution          true
% 12.04/1.96  --res_orphan_elimination                true
% 12.04/1.96  --res_time_limit                        2.
% 12.04/1.96  --res_out_proof                         true
% 12.04/1.96  
% 12.04/1.96  ------ Superposition Options
% 12.04/1.96  
% 12.04/1.96  --superposition_flag                    true
% 12.04/1.96  --sup_passive_queue_type                priority_queues
% 12.04/1.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.04/1.96  --sup_passive_queues_freq               [8;1;4]
% 12.04/1.96  --demod_completeness_check              fast
% 12.04/1.96  --demod_use_ground                      true
% 12.04/1.96  --sup_to_prop_solver                    passive
% 12.04/1.96  --sup_prop_simpl_new                    true
% 12.04/1.96  --sup_prop_simpl_given                  true
% 12.04/1.96  --sup_fun_splitting                     true
% 12.04/1.96  --sup_smt_interval                      50000
% 12.04/1.96  
% 12.04/1.96  ------ Superposition Simplification Setup
% 12.04/1.96  
% 12.04/1.96  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 12.04/1.96  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 12.04/1.96  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 12.04/1.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 12.04/1.96  --sup_full_triv                         [TrivRules;PropSubs]
% 12.04/1.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 12.04/1.96  --sup_full_bw                           [BwDemod;BwSubsumption]
% 12.04/1.96  --sup_immed_triv                        [TrivRules]
% 12.04/1.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.04/1.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.04/1.96  --sup_immed_bw_main                     []
% 12.04/1.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 12.04/1.96  --sup_input_triv                        [Unflattening;TrivRules]
% 12.04/1.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.04/1.96  --sup_input_bw                          []
% 12.04/1.96  
% 12.04/1.96  ------ Combination Options
% 12.04/1.96  
% 12.04/1.96  --comb_res_mult                         3
% 12.04/1.96  --comb_sup_mult                         2
% 12.04/1.96  --comb_inst_mult                        10
% 12.04/1.96  
% 12.04/1.96  ------ Debug Options
% 12.04/1.96  
% 12.04/1.96  --dbg_backtrace                         false
% 12.04/1.96  --dbg_dump_prop_clauses                 false
% 12.04/1.96  --dbg_dump_prop_clauses_file            -
% 12.04/1.96  --dbg_out_stat                          false
% 12.04/1.96  
% 12.04/1.96  
% 12.04/1.96  
% 12.04/1.96  
% 12.04/1.96  ------ Proving...
% 12.04/1.96  
% 12.04/1.96  
% 12.04/1.96  % SZS status Theorem for theBenchmark.p
% 12.04/1.96  
% 12.04/1.96  % SZS output start CNFRefutation for theBenchmark.p
% 12.04/1.96  
% 12.04/1.96  fof(f2,axiom,(
% 12.04/1.96    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 12.04/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.04/1.96  
% 12.04/1.96  fof(f17,plain,(
% 12.04/1.96    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 12.04/1.96    inference(cnf_transformation,[],[f2])).
% 12.04/1.96  
% 12.04/1.96  fof(f9,axiom,(
% 12.04/1.96    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 12.04/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.04/1.96  
% 12.04/1.96  fof(f24,plain,(
% 12.04/1.96    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 12.04/1.96    inference(cnf_transformation,[],[f9])).
% 12.04/1.96  
% 12.04/1.96  fof(f6,axiom,(
% 12.04/1.96    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 12.04/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.04/1.96  
% 12.04/1.96  fof(f21,plain,(
% 12.04/1.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 12.04/1.96    inference(cnf_transformation,[],[f6])).
% 12.04/1.96  
% 12.04/1.96  fof(f1,axiom,(
% 12.04/1.96    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 12.04/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.04/1.96  
% 12.04/1.96  fof(f16,plain,(
% 12.04/1.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 12.04/1.96    inference(cnf_transformation,[],[f1])).
% 12.04/1.96  
% 12.04/1.96  fof(f8,axiom,(
% 12.04/1.96    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 12.04/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.04/1.96  
% 12.04/1.96  fof(f23,plain,(
% 12.04/1.96    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 12.04/1.96    inference(cnf_transformation,[],[f8])).
% 12.04/1.96  
% 12.04/1.96  fof(f3,axiom,(
% 12.04/1.96    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 12.04/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.04/1.96  
% 12.04/1.96  fof(f18,plain,(
% 12.04/1.96    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 12.04/1.96    inference(cnf_transformation,[],[f3])).
% 12.04/1.96  
% 12.04/1.96  fof(f5,axiom,(
% 12.04/1.96    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 12.04/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.04/1.96  
% 12.04/1.96  fof(f12,plain,(
% 12.04/1.96    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 12.04/1.96    inference(ennf_transformation,[],[f5])).
% 12.04/1.96  
% 12.04/1.96  fof(f20,plain,(
% 12.04/1.96    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 12.04/1.96    inference(cnf_transformation,[],[f12])).
% 12.04/1.96  
% 12.04/1.96  fof(f7,axiom,(
% 12.04/1.96    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 12.04/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.04/1.96  
% 12.04/1.96  fof(f22,plain,(
% 12.04/1.96    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 12.04/1.96    inference(cnf_transformation,[],[f7])).
% 12.04/1.96  
% 12.04/1.96  fof(f4,axiom,(
% 12.04/1.96    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 12.04/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.04/1.96  
% 12.04/1.96  fof(f19,plain,(
% 12.04/1.96    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 12.04/1.96    inference(cnf_transformation,[],[f4])).
% 12.04/1.96  
% 12.04/1.96  fof(f10,conjecture,(
% 12.04/1.96    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 12.04/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.04/1.96  
% 12.04/1.96  fof(f11,negated_conjecture,(
% 12.04/1.96    ~! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 12.04/1.96    inference(negated_conjecture,[],[f10])).
% 12.04/1.96  
% 12.04/1.96  fof(f13,plain,(
% 12.04/1.96    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 12.04/1.96    inference(ennf_transformation,[],[f11])).
% 12.04/1.96  
% 12.04/1.96  fof(f14,plain,(
% 12.04/1.96    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 12.04/1.96    introduced(choice_axiom,[])).
% 12.04/1.96  
% 12.04/1.96  fof(f15,plain,(
% 12.04/1.96    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 12.04/1.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 12.04/1.96  
% 12.04/1.96  fof(f25,plain,(
% 12.04/1.96    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 12.04/1.96    inference(cnf_transformation,[],[f15])).
% 12.04/1.96  
% 12.04/1.96  cnf(c_1,plain,
% 12.04/1.96      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 12.04/1.96      inference(cnf_transformation,[],[f17]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_8,plain,
% 12.04/1.96      ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 12.04/1.96      inference(cnf_transformation,[],[f24]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_303,plain,
% 12.04/1.96      ( k4_xboole_0(X0,k3_xboole_0(X1,X0)) = k4_xboole_0(X0,X1) ),
% 12.04/1.96      inference(superposition,[status(thm)],[c_1,c_8]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_5,plain,
% 12.04/1.96      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 12.04/1.96      inference(cnf_transformation,[],[f21]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_0,plain,
% 12.04/1.96      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 12.04/1.96      inference(cnf_transformation,[],[f16]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_7,plain,
% 12.04/1.96      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 12.04/1.96      inference(cnf_transformation,[],[f23]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_250,plain,
% 12.04/1.96      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 12.04/1.96      inference(superposition,[status(thm)],[c_0,c_7]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_629,plain,
% 12.04/1.96      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 12.04/1.96      inference(superposition,[status(thm)],[c_5,c_250]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_637,plain,
% 12.04/1.96      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 12.04/1.96      inference(demodulation,[status(thm)],[c_629,c_250]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_1173,plain,
% 12.04/1.96      ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k4_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 12.04/1.96      inference(superposition,[status(thm)],[c_303,c_637]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_1188,plain,
% 12.04/1.96      ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k4_xboole_0(X0,X1) ),
% 12.04/1.96      inference(light_normalisation,[status(thm)],[c_1173,c_303]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_2,plain,
% 12.04/1.96      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 12.04/1.96      inference(cnf_transformation,[],[f18]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_4,plain,
% 12.04/1.96      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0 ),
% 12.04/1.96      inference(cnf_transformation,[],[f20]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_45,plain,
% 12.04/1.96      ( k4_xboole_0(X0,X1) != X2
% 12.04/1.96      | k3_xboole_0(X2,X3) != X1
% 12.04/1.96      | k1_xboole_0 = X1 ),
% 12.04/1.96      inference(resolution_lifted,[status(thm)],[c_2,c_4]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_46,plain,
% 12.04/1.96      ( k3_xboole_0(k4_xboole_0(X0,X1),X2) != X1 | k1_xboole_0 = X1 ),
% 12.04/1.96      inference(unflattening,[status(thm)],[c_45]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_306,plain,
% 12.04/1.96      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 12.04/1.96      | k3_xboole_0(k4_xboole_0(X0,X1),X2) != k3_xboole_0(X0,X1) ),
% 12.04/1.96      inference(superposition,[status(thm)],[c_8,c_46]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_1544,plain,
% 12.04/1.96      ( k3_xboole_0(k4_xboole_0(X0,X1),X1) != k3_xboole_0(k4_xboole_0(X0,X1),X2)
% 12.04/1.96      | k3_xboole_0(k4_xboole_0(X0,X1),X1) = k1_xboole_0 ),
% 12.04/1.96      inference(superposition,[status(thm)],[c_637,c_306]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_57799,plain,
% 12.04/1.96      ( k3_xboole_0(k4_xboole_0(X0,X1),X1) = k1_xboole_0 ),
% 12.04/1.96      inference(equality_resolution,[status(thm)],[c_1544]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_60506,plain,
% 12.04/1.96      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 12.04/1.96      inference(superposition,[status(thm)],[c_57799,c_303]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_6,plain,
% 12.04/1.96      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 12.04/1.96      inference(cnf_transformation,[],[f22]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_60518,plain,
% 12.04/1.96      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 12.04/1.96      inference(light_normalisation,[status(thm)],[c_60506,c_6]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_252,plain,
% 12.04/1.96      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 12.04/1.96      inference(superposition,[status(thm)],[c_5,c_7]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_61180,plain,
% 12.04/1.96      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 12.04/1.96      inference(demodulation,[status(thm)],[c_60518,c_252]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_63367,plain,
% 12.04/1.96      ( k4_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
% 12.04/1.96      inference(superposition,[status(thm)],[c_1188,c_61180]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_3,plain,
% 12.04/1.96      ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 12.04/1.96      inference(cnf_transformation,[],[f19]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_632,plain,
% 12.04/1.96      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 12.04/1.96      inference(superposition,[status(thm)],[c_250,c_5]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_635,plain,
% 12.04/1.96      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 12.04/1.96      inference(light_normalisation,[status(thm)],[c_632,c_5]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_253,plain,
% 12.04/1.96      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 12.04/1.96      inference(superposition,[status(thm)],[c_7,c_5]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_256,plain,
% 12.04/1.96      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 12.04/1.96      inference(light_normalisation,[status(thm)],[c_253,c_5]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_930,plain,
% 12.04/1.96      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 12.04/1.96      inference(superposition,[status(thm)],[c_635,c_256]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_254,plain,
% 12.04/1.96      ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
% 12.04/1.96      inference(superposition,[status(thm)],[c_7,c_6]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_255,plain,
% 12.04/1.96      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 12.04/1.96      inference(light_normalisation,[status(thm)],[c_254,c_6]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_364,plain,
% 12.04/1.96      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 12.04/1.96      inference(superposition,[status(thm)],[c_0,c_255]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_374,plain,
% 12.04/1.96      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
% 12.04/1.96      inference(superposition,[status(thm)],[c_364,c_7]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_377,plain,
% 12.04/1.96      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 12.04/1.96      inference(superposition,[status(thm)],[c_364,c_3]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_454,plain,
% 12.04/1.96      ( k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 12.04/1.96      inference(superposition,[status(thm)],[c_377,c_8]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_459,plain,
% 12.04/1.96      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 12.04/1.96      inference(demodulation,[status(thm)],[c_454,c_6]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_512,plain,
% 12.04/1.96      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 12.04/1.96      inference(light_normalisation,[status(thm)],[c_374,c_459]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_514,plain,
% 12.04/1.96      ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
% 12.04/1.96      inference(superposition,[status(thm)],[c_512,c_5]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_516,plain,
% 12.04/1.96      ( k2_xboole_0(X0,X0) = X0 ),
% 12.04/1.96      inference(light_normalisation,[status(thm)],[c_514,c_255]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_931,plain,
% 12.04/1.96      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 12.04/1.96      inference(demodulation,[status(thm)],[c_930,c_516]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_1195,plain,
% 12.04/1.96      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 12.04/1.96      inference(superposition,[status(thm)],[c_0,c_931]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_1568,plain,
% 12.04/1.96      ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 12.04/1.96      inference(superposition,[status(thm)],[c_3,c_1195]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_1600,plain,
% 12.04/1.96      ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
% 12.04/1.96      inference(light_normalisation,[status(thm)],[c_1568,c_3]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_305,plain,
% 12.04/1.96      ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(k3_xboole_0(X0,X1),X0) ),
% 12.04/1.96      inference(superposition,[status(thm)],[c_8,c_5]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_1681,plain,
% 12.04/1.96      ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
% 12.04/1.96      inference(demodulation,[status(thm)],[c_1600,c_305]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_2339,plain,
% 12.04/1.96      ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X1 ),
% 12.04/1.96      inference(superposition,[status(thm)],[c_1,c_1681]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_63592,plain,
% 12.04/1.96      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
% 12.04/1.96      inference(light_normalisation,[status(thm)],[c_63367,c_2339]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_9,negated_conjecture,
% 12.04/1.96      ( k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 12.04/1.96      inference(cnf_transformation,[],[f25]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_65120,plain,
% 12.04/1.96      ( k3_xboole_0(sK1,sK0) != k3_xboole_0(sK0,sK1) ),
% 12.04/1.96      inference(demodulation,[status(thm)],[c_63592,c_9]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(c_155,plain,
% 12.04/1.96      ( k3_xboole_0(sK1,sK0) = k3_xboole_0(sK0,sK1) ),
% 12.04/1.96      inference(instantiation,[status(thm)],[c_1]) ).
% 12.04/1.96  
% 12.04/1.96  cnf(contradiction,plain,
% 12.04/1.96      ( $false ),
% 12.04/1.96      inference(minisat,[status(thm)],[c_65120,c_155]) ).
% 12.04/1.96  
% 12.04/1.96  
% 12.04/1.96  % SZS output end CNFRefutation for theBenchmark.p
% 12.04/1.96  
% 12.04/1.96  ------                               Statistics
% 12.04/1.96  
% 12.04/1.96  ------ General
% 12.04/1.96  
% 12.04/1.96  abstr_ref_over_cycles:                  0
% 12.04/1.96  abstr_ref_under_cycles:                 0
% 12.04/1.96  gc_basic_clause_elim:                   0
% 12.04/1.96  forced_gc_time:                         0
% 12.04/1.96  parsing_time:                           0.008
% 12.04/1.96  unif_index_cands_time:                  0.
% 12.04/1.96  unif_index_add_time:                    0.
% 12.04/1.96  orderings_time:                         0.
% 12.04/1.96  out_proof_time:                         0.006
% 12.04/1.96  total_time:                             1.494
% 12.04/1.96  num_of_symbols:                         38
% 12.04/1.96  num_of_terms:                           66531
% 12.04/1.96  
% 12.04/1.96  ------ Preprocessing
% 12.04/1.96  
% 12.04/1.96  num_of_splits:                          0
% 12.04/1.96  num_of_split_atoms:                     0
% 12.04/1.96  num_of_reused_defs:                     0
% 12.04/1.96  num_eq_ax_congr_red:                    3
% 12.04/1.96  num_of_sem_filtered_clauses:            0
% 12.04/1.96  num_of_subtypes:                        0
% 12.04/1.96  monotx_restored_types:                  0
% 12.04/1.96  sat_num_of_epr_types:                   0
% 12.04/1.96  sat_num_of_non_cyclic_types:            0
% 12.04/1.96  sat_guarded_non_collapsed_types:        0
% 12.04/1.96  num_pure_diseq_elim:                    0
% 12.04/1.96  simp_replaced_by:                       0
% 12.04/1.96  res_preprocessed:                       33
% 12.04/1.96  prep_upred:                             0
% 12.04/1.96  prep_unflattend:                        1
% 12.04/1.96  smt_new_axioms:                         0
% 12.04/1.96  pred_elim_cands:                        0
% 12.04/1.96  pred_elim:                              1
% 12.04/1.96  pred_elim_cl:                           1
% 12.04/1.96  pred_elim_cycles:                       2
% 12.04/1.96  merged_defs:                            0
% 12.04/1.96  merged_defs_ncl:                        0
% 12.04/1.96  bin_hyper_res:                          0
% 12.04/1.96  prep_cycles:                            3
% 12.04/1.96  pred_elim_time:                         0.
% 12.04/1.96  splitting_time:                         0.
% 12.04/1.96  sem_filter_time:                        0.
% 12.04/1.96  monotx_time:                            0.
% 12.04/1.96  subtype_inf_time:                       0.
% 12.04/1.96  
% 12.04/1.96  ------ Problem properties
% 12.04/1.96  
% 12.04/1.96  clauses:                                9
% 12.04/1.96  conjectures:                            1
% 12.04/1.96  epr:                                    0
% 12.04/1.96  horn:                                   9
% 12.04/1.96  ground:                                 1
% 12.04/1.96  unary:                                  8
% 12.04/1.96  binary:                                 1
% 12.04/1.96  lits:                                   10
% 12.04/1.96  lits_eq:                                10
% 12.04/1.96  fd_pure:                                0
% 12.04/1.96  fd_pseudo:                              0
% 12.04/1.96  fd_cond:                                1
% 12.04/1.96  fd_pseudo_cond:                         0
% 12.04/1.96  ac_symbols:                             0
% 12.04/1.96  
% 12.04/1.96  ------ Propositional Solver
% 12.04/1.96  
% 12.04/1.96  prop_solver_calls:                      29
% 12.04/1.96  prop_fast_solver_calls:                 432
% 12.04/1.96  smt_solver_calls:                       0
% 12.04/1.96  smt_fast_solver_calls:                  0
% 12.04/1.96  prop_num_of_clauses:                    6311
% 12.04/1.96  prop_preprocess_simplified:             12016
% 12.04/1.96  prop_fo_subsumed:                       0
% 12.04/1.96  prop_solver_time:                       0.
% 12.04/1.96  smt_solver_time:                        0.
% 12.04/1.96  smt_fast_solver_time:                   0.
% 12.04/1.96  prop_fast_solver_time:                  0.
% 12.04/1.96  prop_unsat_core_time:                   0.
% 12.04/1.96  
% 12.04/1.96  ------ QBF
% 12.04/1.96  
% 12.04/1.96  qbf_q_res:                              0
% 12.04/1.96  qbf_num_tautologies:                    0
% 12.04/1.96  qbf_prep_cycles:                        0
% 12.04/1.96  
% 12.04/1.96  ------ BMC1
% 12.04/1.96  
% 12.04/1.96  bmc1_current_bound:                     -1
% 12.04/1.96  bmc1_last_solved_bound:                 -1
% 12.04/1.96  bmc1_unsat_core_size:                   -1
% 12.04/1.96  bmc1_unsat_core_parents_size:           -1
% 12.04/1.96  bmc1_merge_next_fun:                    0
% 12.04/1.96  bmc1_unsat_core_clauses_time:           0.
% 12.04/1.96  
% 12.04/1.96  ------ Instantiation
% 12.04/1.96  
% 12.04/1.96  inst_num_of_clauses:                    3084
% 12.04/1.96  inst_num_in_passive:                    1114
% 12.04/1.96  inst_num_in_active:                     1065
% 12.04/1.96  inst_num_in_unprocessed:                905
% 12.04/1.96  inst_num_of_loops:                      1140
% 12.04/1.96  inst_num_of_learning_restarts:          0
% 12.04/1.96  inst_num_moves_active_passive:          71
% 12.04/1.96  inst_lit_activity:                      0
% 12.04/1.96  inst_lit_activity_moves:                0
% 12.04/1.96  inst_num_tautologies:                   0
% 12.04/1.96  inst_num_prop_implied:                  0
% 12.04/1.96  inst_num_existing_simplified:           0
% 12.04/1.96  inst_num_eq_res_simplified:             0
% 12.04/1.96  inst_num_child_elim:                    0
% 12.04/1.96  inst_num_of_dismatching_blockings:      1101
% 12.04/1.96  inst_num_of_non_proper_insts:           4003
% 12.04/1.96  inst_num_of_duplicates:                 0
% 12.04/1.96  inst_inst_num_from_inst_to_res:         0
% 12.04/1.96  inst_dismatching_checking_time:         0.
% 12.04/1.96  
% 12.04/1.96  ------ Resolution
% 12.04/1.96  
% 12.04/1.96  res_num_of_clauses:                     0
% 12.04/1.96  res_num_in_passive:                     0
% 12.04/1.96  res_num_in_active:                      0
% 12.04/1.96  res_num_of_loops:                       36
% 12.04/1.96  res_forward_subset_subsumed:            1819
% 12.04/1.96  res_backward_subset_subsumed:           6
% 12.04/1.96  res_forward_subsumed:                   0
% 12.04/1.96  res_backward_subsumed:                  0
% 12.04/1.96  res_forward_subsumption_resolution:     0
% 12.04/1.96  res_backward_subsumption_resolution:    0
% 12.04/1.96  res_clause_to_clause_subsumption:       47139
% 12.04/1.96  res_orphan_elimination:                 0
% 12.04/1.96  res_tautology_del:                      406
% 12.04/1.96  res_num_eq_res_simplified:              0
% 12.04/1.96  res_num_sel_changes:                    0
% 12.04/1.96  res_moves_from_active_to_pass:          0
% 12.04/1.96  
% 12.04/1.96  ------ Superposition
% 12.04/1.96  
% 12.04/1.96  sup_time_total:                         0.
% 12.04/1.96  sup_time_generating:                    0.
% 12.04/1.96  sup_time_sim_full:                      0.
% 12.04/1.96  sup_time_sim_immed:                     0.
% 12.04/1.96  
% 12.04/1.96  sup_num_of_clauses:                     1139
% 12.04/1.96  sup_num_in_active:                      114
% 12.04/1.96  sup_num_in_passive:                     1025
% 12.04/1.96  sup_num_of_loops:                       227
% 12.04/1.96  sup_fw_superposition:                   16048
% 12.04/1.96  sup_bw_superposition:                   11483
% 12.04/1.96  sup_immediate_simplified:               18896
% 12.04/1.96  sup_given_eliminated:                   7
% 12.04/1.96  comparisons_done:                       0
% 12.04/1.96  comparisons_avoided:                    0
% 12.04/1.96  
% 12.04/1.96  ------ Simplifications
% 12.04/1.96  
% 12.04/1.96  
% 12.04/1.96  sim_fw_subset_subsumed:                 131
% 12.04/1.96  sim_bw_subset_subsumed:                 1
% 12.04/1.96  sim_fw_subsumed:                        2257
% 12.04/1.96  sim_bw_subsumed:                        3
% 12.04/1.96  sim_fw_subsumption_res:                 0
% 12.04/1.96  sim_bw_subsumption_res:                 0
% 12.04/1.96  sim_tautology_del:                      689
% 12.04/1.96  sim_eq_tautology_del:                   8014
% 12.04/1.96  sim_eq_res_simp:                        0
% 12.04/1.96  sim_fw_demodulated:                     12126
% 12.04/1.96  sim_bw_demodulated:                     288
% 12.04/1.96  sim_light_normalised:                   12095
% 12.04/1.96  sim_joinable_taut:                      0
% 12.04/1.96  sim_joinable_simp:                      0
% 12.04/1.96  sim_ac_normalised:                      0
% 12.04/1.96  sim_smt_subsumption:                    0
% 12.04/1.96  
%------------------------------------------------------------------------------
