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
% DateTime   : Thu Dec  3 11:51:26 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 136 expanded)
%              Number of clauses        :   34 (  49 expanded)
%              Number of leaves         :   10 (  29 expanded)
%              Depth                    :   14
%              Number of atoms          :  134 ( 297 expanded)
%              Number of equality atoms :   71 ( 145 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = k1_xboole_0 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
    ? [X1] :
      ( k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f18,plain,(
    ! [X0] :
    ? [X1] :
      ( k1_relat_1(X1) = X0
      & v1_relat_1(X1) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_relat_1(X1) = X0
          & v1_relat_1(X1) )
     => ( k1_relat_1(sK1(X0)) = X0
        & v1_relat_1(sK1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( k1_relat_1(sK1(X0)) = X0
      & v1_relat_1(sK1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f31])).

fof(f46,plain,(
    ! [X0] : v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) != k10_relat_1(k7_relat_1(X2,X0),X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(X0,k10_relat_1(X2,X1)) != k10_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(X2) )
   => ( k3_xboole_0(sK2,k10_relat_1(sK4,sK3)) != k10_relat_1(k7_relat_1(sK4,sK2),sK3)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( k3_xboole_0(sK2,k10_relat_1(sK4,sK3)) != k10_relat_1(k7_relat_1(sK4,sK2),sK3)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f33])).

fof(f48,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    ! [X0] : k1_relat_1(sK1(X0)) = X0 ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    k3_xboole_0(sK2,k10_relat_1(sK4,sK3)) != k10_relat_1(k7_relat_1(sK4,sK2),sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_12,plain,
    ( v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_251,plain,
    ( v1_relat_1(sK1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_250,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_257,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_255,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1018,plain,
    ( k10_relat_1(k7_relat_1(X0,X1),k1_relat_1(X2)) = k1_relat_1(k5_relat_1(k7_relat_1(X0,X1),X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_257,c_255])).

cnf(c_4207,plain,
    ( k10_relat_1(k7_relat_1(sK4,X0),k1_relat_1(X1)) = k1_relat_1(k5_relat_1(k7_relat_1(sK4,X0),X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_250,c_1018])).

cnf(c_11889,plain,
    ( k10_relat_1(k7_relat_1(sK4,X0),k1_relat_1(sK1(X1))) = k1_relat_1(k5_relat_1(k7_relat_1(sK4,X0),sK1(X1))) ),
    inference(superposition,[status(thm)],[c_251,c_4207])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_258,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_253,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_852,plain,
    ( k1_relat_1(k7_relat_1(k5_relat_1(X0,X1),X2)) = k3_xboole_0(k1_relat_1(k5_relat_1(X0,X1)),X2)
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_258,c_253])).

cnf(c_1692,plain,
    ( k1_relat_1(k7_relat_1(k5_relat_1(sK4,X0),X1)) = k3_xboole_0(k1_relat_1(k5_relat_1(sK4,X0)),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_250,c_852])).

cnf(c_10781,plain,
    ( k1_relat_1(k7_relat_1(k5_relat_1(sK4,sK1(X0)),X1)) = k3_xboole_0(k1_relat_1(k5_relat_1(sK4,sK1(X0))),X1) ),
    inference(superposition,[status(thm)],[c_251,c_1692])).

cnf(c_1021,plain,
    ( k10_relat_1(sK4,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK4,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_250,c_255])).

cnf(c_5679,plain,
    ( k10_relat_1(sK4,k1_relat_1(sK1(X0))) = k1_relat_1(k5_relat_1(sK4,sK1(X0))) ),
    inference(superposition,[status(thm)],[c_251,c_1021])).

cnf(c_11,plain,
    ( k1_relat_1(sK1(X0)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_5684,plain,
    ( k1_relat_1(k5_relat_1(sK4,sK1(X0))) = k10_relat_1(sK4,X0) ),
    inference(light_normalisation,[status(thm)],[c_5679,c_11])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_256,plain,
    ( k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1069,plain,
    ( k7_relat_1(k5_relat_1(sK4,X0),X1) = k5_relat_1(k7_relat_1(sK4,X1),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_250,c_256])).

cnf(c_7537,plain,
    ( k7_relat_1(k5_relat_1(sK4,sK1(X0)),X1) = k5_relat_1(k7_relat_1(sK4,X1),sK1(X0)) ),
    inference(superposition,[status(thm)],[c_251,c_1069])).

cnf(c_10810,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1(sK4,X0),sK1(X1))) = k3_xboole_0(k10_relat_1(sK4,X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_10781,c_5684,c_7537])).

cnf(c_11919,plain,
    ( k10_relat_1(k7_relat_1(sK4,X0),k1_relat_1(sK1(X1))) = k3_xboole_0(k10_relat_1(sK4,X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_11889,c_10810])).

cnf(c_11920,plain,
    ( k10_relat_1(k7_relat_1(sK4,X0),X1) = k3_xboole_0(k10_relat_1(sK4,X1),X0) ),
    inference(demodulation,[status(thm)],[c_11919,c_11])).

cnf(c_13,negated_conjecture,
    ( k3_xboole_0(sK2,k10_relat_1(sK4,sK3)) != k10_relat_1(k7_relat_1(sK4,sK2),sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_11954,plain,
    ( k3_xboole_0(k10_relat_1(sK4,sK3),sK2) != k3_xboole_0(sK2,k10_relat_1(sK4,sK3)) ),
    inference(demodulation,[status(thm)],[c_11920,c_13])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_5625,plain,
    ( k3_xboole_0(k10_relat_1(sK4,sK3),sK2) = k3_xboole_0(sK2,k10_relat_1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11954,c_5625])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:14:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.71/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.71/1.00  
% 3.71/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.71/1.00  
% 3.71/1.00  ------  iProver source info
% 3.71/1.00  
% 3.71/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.71/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.71/1.00  git: non_committed_changes: false
% 3.71/1.00  git: last_make_outside_of_git: false
% 3.71/1.00  
% 3.71/1.00  ------ 
% 3.71/1.00  
% 3.71/1.00  ------ Input Options
% 3.71/1.00  
% 3.71/1.00  --out_options                           all
% 3.71/1.00  --tptp_safe_out                         true
% 3.71/1.00  --problem_path                          ""
% 3.71/1.00  --include_path                          ""
% 3.71/1.00  --clausifier                            res/vclausify_rel
% 3.71/1.00  --clausifier_options                    --mode clausify
% 3.71/1.00  --stdin                                 false
% 3.71/1.00  --stats_out                             sel
% 3.71/1.00  
% 3.71/1.00  ------ General Options
% 3.71/1.00  
% 3.71/1.00  --fof                                   false
% 3.71/1.00  --time_out_real                         604.99
% 3.71/1.00  --time_out_virtual                      -1.
% 3.71/1.00  --symbol_type_check                     false
% 3.71/1.00  --clausify_out                          false
% 3.71/1.00  --sig_cnt_out                           false
% 3.71/1.00  --trig_cnt_out                          false
% 3.71/1.00  --trig_cnt_out_tolerance                1.
% 3.71/1.00  --trig_cnt_out_sk_spl                   false
% 3.71/1.00  --abstr_cl_out                          false
% 3.71/1.00  
% 3.71/1.00  ------ Global Options
% 3.71/1.00  
% 3.71/1.00  --schedule                              none
% 3.71/1.00  --add_important_lit                     false
% 3.71/1.00  --prop_solver_per_cl                    1000
% 3.71/1.00  --min_unsat_core                        false
% 3.71/1.00  --soft_assumptions                      false
% 3.71/1.00  --soft_lemma_size                       3
% 3.71/1.00  --prop_impl_unit_size                   0
% 3.71/1.00  --prop_impl_unit                        []
% 3.71/1.00  --share_sel_clauses                     true
% 3.71/1.00  --reset_solvers                         false
% 3.71/1.00  --bc_imp_inh                            [conj_cone]
% 3.71/1.00  --conj_cone_tolerance                   3.
% 3.71/1.00  --extra_neg_conj                        none
% 3.71/1.00  --large_theory_mode                     true
% 3.71/1.00  --prolific_symb_bound                   200
% 3.71/1.00  --lt_threshold                          2000
% 3.71/1.00  --clause_weak_htbl                      true
% 3.71/1.00  --gc_record_bc_elim                     false
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing Options
% 3.71/1.00  
% 3.71/1.00  --preprocessing_flag                    true
% 3.71/1.00  --time_out_prep_mult                    0.1
% 3.71/1.00  --splitting_mode                        input
% 3.71/1.00  --splitting_grd                         true
% 3.71/1.00  --splitting_cvd                         false
% 3.71/1.00  --splitting_cvd_svl                     false
% 3.71/1.00  --splitting_nvd                         32
% 3.71/1.00  --sub_typing                            true
% 3.71/1.00  --prep_gs_sim                           false
% 3.71/1.00  --prep_unflatten                        true
% 3.71/1.00  --prep_res_sim                          true
% 3.71/1.00  --prep_upred                            true
% 3.71/1.00  --prep_sem_filter                       exhaustive
% 3.71/1.00  --prep_sem_filter_out                   false
% 3.71/1.00  --pred_elim                             false
% 3.71/1.00  --res_sim_input                         true
% 3.71/1.00  --eq_ax_congr_red                       true
% 3.71/1.00  --pure_diseq_elim                       true
% 3.71/1.00  --brand_transform                       false
% 3.71/1.00  --non_eq_to_eq                          false
% 3.71/1.00  --prep_def_merge                        true
% 3.71/1.00  --prep_def_merge_prop_impl              false
% 3.71/1.00  --prep_def_merge_mbd                    true
% 3.71/1.00  --prep_def_merge_tr_red                 false
% 3.71/1.00  --prep_def_merge_tr_cl                  false
% 3.71/1.00  --smt_preprocessing                     true
% 3.71/1.00  --smt_ac_axioms                         fast
% 3.71/1.00  --preprocessed_out                      false
% 3.71/1.00  --preprocessed_stats                    false
% 3.71/1.00  
% 3.71/1.00  ------ Abstraction refinement Options
% 3.71/1.00  
% 3.71/1.00  --abstr_ref                             []
% 3.71/1.00  --abstr_ref_prep                        false
% 3.71/1.00  --abstr_ref_until_sat                   false
% 3.71/1.00  --abstr_ref_sig_restrict                funpre
% 3.71/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.71/1.00  --abstr_ref_under                       []
% 3.71/1.00  
% 3.71/1.00  ------ SAT Options
% 3.71/1.00  
% 3.71/1.00  --sat_mode                              false
% 3.71/1.00  --sat_fm_restart_options                ""
% 3.71/1.00  --sat_gr_def                            false
% 3.71/1.00  --sat_epr_types                         true
% 3.71/1.00  --sat_non_cyclic_types                  false
% 3.71/1.00  --sat_finite_models                     false
% 3.71/1.00  --sat_fm_lemmas                         false
% 3.71/1.00  --sat_fm_prep                           false
% 3.71/1.00  --sat_fm_uc_incr                        true
% 3.71/1.00  --sat_out_model                         small
% 3.71/1.00  --sat_out_clauses                       false
% 3.71/1.00  
% 3.71/1.00  ------ QBF Options
% 3.71/1.00  
% 3.71/1.00  --qbf_mode                              false
% 3.71/1.00  --qbf_elim_univ                         false
% 3.71/1.00  --qbf_dom_inst                          none
% 3.71/1.00  --qbf_dom_pre_inst                      false
% 3.71/1.00  --qbf_sk_in                             false
% 3.71/1.00  --qbf_pred_elim                         true
% 3.71/1.00  --qbf_split                             512
% 3.71/1.00  
% 3.71/1.00  ------ BMC1 Options
% 3.71/1.00  
% 3.71/1.00  --bmc1_incremental                      false
% 3.71/1.00  --bmc1_axioms                           reachable_all
% 3.71/1.00  --bmc1_min_bound                        0
% 3.71/1.00  --bmc1_max_bound                        -1
% 3.71/1.00  --bmc1_max_bound_default                -1
% 3.71/1.00  --bmc1_symbol_reachability              true
% 3.71/1.00  --bmc1_property_lemmas                  false
% 3.71/1.00  --bmc1_k_induction                      false
% 3.71/1.00  --bmc1_non_equiv_states                 false
% 3.71/1.00  --bmc1_deadlock                         false
% 3.71/1.00  --bmc1_ucm                              false
% 3.71/1.00  --bmc1_add_unsat_core                   none
% 3.71/1.00  --bmc1_unsat_core_children              false
% 3.71/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.71/1.00  --bmc1_out_stat                         full
% 3.71/1.00  --bmc1_ground_init                      false
% 3.71/1.00  --bmc1_pre_inst_next_state              false
% 3.71/1.00  --bmc1_pre_inst_state                   false
% 3.71/1.00  --bmc1_pre_inst_reach_state             false
% 3.71/1.00  --bmc1_out_unsat_core                   false
% 3.71/1.00  --bmc1_aig_witness_out                  false
% 3.71/1.00  --bmc1_verbose                          false
% 3.71/1.00  --bmc1_dump_clauses_tptp                false
% 3.71/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.71/1.00  --bmc1_dump_file                        -
% 3.71/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.71/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.71/1.00  --bmc1_ucm_extend_mode                  1
% 3.71/1.00  --bmc1_ucm_init_mode                    2
% 3.71/1.00  --bmc1_ucm_cone_mode                    none
% 3.71/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.71/1.00  --bmc1_ucm_relax_model                  4
% 3.71/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.71/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.71/1.00  --bmc1_ucm_layered_model                none
% 3.71/1.00  --bmc1_ucm_max_lemma_size               10
% 3.71/1.00  
% 3.71/1.00  ------ AIG Options
% 3.71/1.00  
% 3.71/1.00  --aig_mode                              false
% 3.71/1.00  
% 3.71/1.00  ------ Instantiation Options
% 3.71/1.00  
% 3.71/1.00  --instantiation_flag                    true
% 3.71/1.00  --inst_sos_flag                         false
% 3.71/1.00  --inst_sos_phase                        true
% 3.71/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.71/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.71/1.00  --inst_lit_sel_side                     num_symb
% 3.71/1.00  --inst_solver_per_active                1400
% 3.71/1.00  --inst_solver_calls_frac                1.
% 3.71/1.00  --inst_passive_queue_type               priority_queues
% 3.71/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.71/1.00  --inst_passive_queues_freq              [25;2]
% 3.71/1.00  --inst_dismatching                      true
% 3.71/1.00  --inst_eager_unprocessed_to_passive     true
% 3.71/1.00  --inst_prop_sim_given                   true
% 3.71/1.00  --inst_prop_sim_new                     false
% 3.71/1.00  --inst_subs_new                         false
% 3.71/1.00  --inst_eq_res_simp                      false
% 3.71/1.00  --inst_subs_given                       false
% 3.71/1.00  --inst_orphan_elimination               true
% 3.71/1.00  --inst_learning_loop_flag               true
% 3.71/1.00  --inst_learning_start                   3000
% 3.71/1.00  --inst_learning_factor                  2
% 3.71/1.00  --inst_start_prop_sim_after_learn       3
% 3.71/1.00  --inst_sel_renew                        solver
% 3.71/1.00  --inst_lit_activity_flag                true
% 3.71/1.00  --inst_restr_to_given                   false
% 3.71/1.00  --inst_activity_threshold               500
% 3.71/1.00  --inst_out_proof                        true
% 3.71/1.00  
% 3.71/1.00  ------ Resolution Options
% 3.71/1.00  
% 3.71/1.00  --resolution_flag                       true
% 3.71/1.00  --res_lit_sel                           adaptive
% 3.71/1.00  --res_lit_sel_side                      none
% 3.71/1.00  --res_ordering                          kbo
% 3.71/1.00  --res_to_prop_solver                    active
% 3.71/1.00  --res_prop_simpl_new                    false
% 3.71/1.00  --res_prop_simpl_given                  true
% 3.71/1.00  --res_passive_queue_type                priority_queues
% 3.71/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.71/1.00  --res_passive_queues_freq               [15;5]
% 3.71/1.00  --res_forward_subs                      full
% 3.71/1.00  --res_backward_subs                     full
% 3.71/1.00  --res_forward_subs_resolution           true
% 3.71/1.00  --res_backward_subs_resolution          true
% 3.71/1.00  --res_orphan_elimination                true
% 3.71/1.00  --res_time_limit                        2.
% 3.71/1.00  --res_out_proof                         true
% 3.71/1.00  
% 3.71/1.00  ------ Superposition Options
% 3.71/1.00  
% 3.71/1.00  --superposition_flag                    true
% 3.71/1.00  --sup_passive_queue_type                priority_queues
% 3.71/1.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.71/1.00  --sup_passive_queues_freq               [1;4]
% 3.71/1.00  --demod_completeness_check              fast
% 3.71/1.00  --demod_use_ground                      true
% 3.71/1.00  --sup_to_prop_solver                    passive
% 3.71/1.00  --sup_prop_simpl_new                    true
% 3.71/1.00  --sup_prop_simpl_given                  true
% 3.71/1.00  --sup_fun_splitting                     false
% 3.71/1.00  --sup_smt_interval                      50000
% 3.71/1.00  
% 3.71/1.00  ------ Superposition Simplification Setup
% 3.71/1.00  
% 3.71/1.00  --sup_indices_passive                   []
% 3.71/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.71/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/1.00  --sup_full_bw                           [BwDemod]
% 3.71/1.00  --sup_immed_triv                        [TrivRules]
% 3.71/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/1.00  --sup_immed_bw_main                     []
% 3.71/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.71/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/1.00  
% 3.71/1.00  ------ Combination Options
% 3.71/1.00  
% 3.71/1.00  --comb_res_mult                         3
% 3.71/1.00  --comb_sup_mult                         2
% 3.71/1.00  --comb_inst_mult                        10
% 3.71/1.00  
% 3.71/1.00  ------ Debug Options
% 3.71/1.00  
% 3.71/1.00  --dbg_backtrace                         false
% 3.71/1.00  --dbg_dump_prop_clauses                 false
% 3.71/1.00  --dbg_dump_prop_clauses_file            -
% 3.71/1.00  --dbg_out_stat                          false
% 3.71/1.00  ------ Parsing...
% 3.71/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.71/1.00  ------ Proving...
% 3.71/1.00  ------ Problem Properties 
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  clauses                                 15
% 3.71/1.00  conjectures                             2
% 3.71/1.00  EPR                                     1
% 3.71/1.00  Horn                                    15
% 3.71/1.00  unary                                   8
% 3.71/1.00  binary                                  3
% 3.71/1.00  lits                                    28
% 3.71/1.00  lits eq                                 12
% 3.71/1.00  fd_pure                                 0
% 3.71/1.00  fd_pseudo                               0
% 3.71/1.00  fd_cond                                 0
% 3.71/1.00  fd_pseudo_cond                          1
% 3.71/1.00  AC symbols                              0
% 3.71/1.00  
% 3.71/1.00  ------ Input Options Time Limit: Unbounded
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  ------ 
% 3.71/1.00  Current options:
% 3.71/1.00  ------ 
% 3.71/1.00  
% 3.71/1.00  ------ Input Options
% 3.71/1.00  
% 3.71/1.00  --out_options                           all
% 3.71/1.00  --tptp_safe_out                         true
% 3.71/1.00  --problem_path                          ""
% 3.71/1.00  --include_path                          ""
% 3.71/1.00  --clausifier                            res/vclausify_rel
% 3.71/1.00  --clausifier_options                    --mode clausify
% 3.71/1.00  --stdin                                 false
% 3.71/1.00  --stats_out                             sel
% 3.71/1.00  
% 3.71/1.00  ------ General Options
% 3.71/1.00  
% 3.71/1.00  --fof                                   false
% 3.71/1.00  --time_out_real                         604.99
% 3.71/1.00  --time_out_virtual                      -1.
% 3.71/1.00  --symbol_type_check                     false
% 3.71/1.00  --clausify_out                          false
% 3.71/1.00  --sig_cnt_out                           false
% 3.71/1.00  --trig_cnt_out                          false
% 3.71/1.00  --trig_cnt_out_tolerance                1.
% 3.71/1.00  --trig_cnt_out_sk_spl                   false
% 3.71/1.00  --abstr_cl_out                          false
% 3.71/1.00  
% 3.71/1.00  ------ Global Options
% 3.71/1.00  
% 3.71/1.00  --schedule                              none
% 3.71/1.00  --add_important_lit                     false
% 3.71/1.00  --prop_solver_per_cl                    1000
% 3.71/1.00  --min_unsat_core                        false
% 3.71/1.00  --soft_assumptions                      false
% 3.71/1.00  --soft_lemma_size                       3
% 3.71/1.00  --prop_impl_unit_size                   0
% 3.71/1.00  --prop_impl_unit                        []
% 3.71/1.00  --share_sel_clauses                     true
% 3.71/1.00  --reset_solvers                         false
% 3.71/1.00  --bc_imp_inh                            [conj_cone]
% 3.71/1.00  --conj_cone_tolerance                   3.
% 3.71/1.00  --extra_neg_conj                        none
% 3.71/1.00  --large_theory_mode                     true
% 3.71/1.00  --prolific_symb_bound                   200
% 3.71/1.00  --lt_threshold                          2000
% 3.71/1.00  --clause_weak_htbl                      true
% 3.71/1.00  --gc_record_bc_elim                     false
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing Options
% 3.71/1.00  
% 3.71/1.00  --preprocessing_flag                    true
% 3.71/1.00  --time_out_prep_mult                    0.1
% 3.71/1.00  --splitting_mode                        input
% 3.71/1.00  --splitting_grd                         true
% 3.71/1.00  --splitting_cvd                         false
% 3.71/1.00  --splitting_cvd_svl                     false
% 3.71/1.00  --splitting_nvd                         32
% 3.71/1.00  --sub_typing                            true
% 3.71/1.00  --prep_gs_sim                           false
% 3.71/1.00  --prep_unflatten                        true
% 3.71/1.00  --prep_res_sim                          true
% 3.71/1.00  --prep_upred                            true
% 3.71/1.00  --prep_sem_filter                       exhaustive
% 3.71/1.00  --prep_sem_filter_out                   false
% 3.71/1.00  --pred_elim                             false
% 3.71/1.00  --res_sim_input                         true
% 3.71/1.00  --eq_ax_congr_red                       true
% 3.71/1.00  --pure_diseq_elim                       true
% 3.71/1.00  --brand_transform                       false
% 3.71/1.00  --non_eq_to_eq                          false
% 3.71/1.00  --prep_def_merge                        true
% 3.71/1.00  --prep_def_merge_prop_impl              false
% 3.71/1.00  --prep_def_merge_mbd                    true
% 3.71/1.00  --prep_def_merge_tr_red                 false
% 3.71/1.00  --prep_def_merge_tr_cl                  false
% 3.71/1.00  --smt_preprocessing                     true
% 3.71/1.00  --smt_ac_axioms                         fast
% 3.71/1.00  --preprocessed_out                      false
% 3.71/1.00  --preprocessed_stats                    false
% 3.71/1.00  
% 3.71/1.00  ------ Abstraction refinement Options
% 3.71/1.00  
% 3.71/1.00  --abstr_ref                             []
% 3.71/1.00  --abstr_ref_prep                        false
% 3.71/1.00  --abstr_ref_until_sat                   false
% 3.71/1.00  --abstr_ref_sig_restrict                funpre
% 3.71/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.71/1.00  --abstr_ref_under                       []
% 3.71/1.00  
% 3.71/1.00  ------ SAT Options
% 3.71/1.00  
% 3.71/1.00  --sat_mode                              false
% 3.71/1.00  --sat_fm_restart_options                ""
% 3.71/1.00  --sat_gr_def                            false
% 3.71/1.00  --sat_epr_types                         true
% 3.71/1.00  --sat_non_cyclic_types                  false
% 3.71/1.00  --sat_finite_models                     false
% 3.71/1.00  --sat_fm_lemmas                         false
% 3.71/1.00  --sat_fm_prep                           false
% 3.71/1.00  --sat_fm_uc_incr                        true
% 3.71/1.00  --sat_out_model                         small
% 3.71/1.00  --sat_out_clauses                       false
% 3.71/1.00  
% 3.71/1.00  ------ QBF Options
% 3.71/1.00  
% 3.71/1.00  --qbf_mode                              false
% 3.71/1.00  --qbf_elim_univ                         false
% 3.71/1.00  --qbf_dom_inst                          none
% 3.71/1.00  --qbf_dom_pre_inst                      false
% 3.71/1.00  --qbf_sk_in                             false
% 3.71/1.00  --qbf_pred_elim                         true
% 3.71/1.00  --qbf_split                             512
% 3.71/1.00  
% 3.71/1.00  ------ BMC1 Options
% 3.71/1.00  
% 3.71/1.00  --bmc1_incremental                      false
% 3.71/1.00  --bmc1_axioms                           reachable_all
% 3.71/1.00  --bmc1_min_bound                        0
% 3.71/1.00  --bmc1_max_bound                        -1
% 3.71/1.00  --bmc1_max_bound_default                -1
% 3.71/1.00  --bmc1_symbol_reachability              true
% 3.71/1.00  --bmc1_property_lemmas                  false
% 3.71/1.00  --bmc1_k_induction                      false
% 3.71/1.00  --bmc1_non_equiv_states                 false
% 3.71/1.00  --bmc1_deadlock                         false
% 3.71/1.00  --bmc1_ucm                              false
% 3.71/1.00  --bmc1_add_unsat_core                   none
% 3.71/1.00  --bmc1_unsat_core_children              false
% 3.71/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.71/1.00  --bmc1_out_stat                         full
% 3.71/1.00  --bmc1_ground_init                      false
% 3.71/1.00  --bmc1_pre_inst_next_state              false
% 3.71/1.00  --bmc1_pre_inst_state                   false
% 3.71/1.00  --bmc1_pre_inst_reach_state             false
% 3.71/1.00  --bmc1_out_unsat_core                   false
% 3.71/1.00  --bmc1_aig_witness_out                  false
% 3.71/1.00  --bmc1_verbose                          false
% 3.71/1.00  --bmc1_dump_clauses_tptp                false
% 3.71/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.71/1.00  --bmc1_dump_file                        -
% 3.71/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.71/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.71/1.00  --bmc1_ucm_extend_mode                  1
% 3.71/1.00  --bmc1_ucm_init_mode                    2
% 3.71/1.00  --bmc1_ucm_cone_mode                    none
% 3.71/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.71/1.00  --bmc1_ucm_relax_model                  4
% 3.71/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.71/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.71/1.00  --bmc1_ucm_layered_model                none
% 3.71/1.00  --bmc1_ucm_max_lemma_size               10
% 3.71/1.00  
% 3.71/1.00  ------ AIG Options
% 3.71/1.00  
% 3.71/1.00  --aig_mode                              false
% 3.71/1.00  
% 3.71/1.00  ------ Instantiation Options
% 3.71/1.00  
% 3.71/1.00  --instantiation_flag                    true
% 3.71/1.00  --inst_sos_flag                         false
% 3.71/1.00  --inst_sos_phase                        true
% 3.71/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.71/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.71/1.00  --inst_lit_sel_side                     num_symb
% 3.71/1.00  --inst_solver_per_active                1400
% 3.71/1.00  --inst_solver_calls_frac                1.
% 3.71/1.00  --inst_passive_queue_type               priority_queues
% 3.71/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.71/1.00  --inst_passive_queues_freq              [25;2]
% 3.71/1.00  --inst_dismatching                      true
% 3.71/1.00  --inst_eager_unprocessed_to_passive     true
% 3.71/1.00  --inst_prop_sim_given                   true
% 3.71/1.00  --inst_prop_sim_new                     false
% 3.71/1.00  --inst_subs_new                         false
% 3.71/1.00  --inst_eq_res_simp                      false
% 3.71/1.00  --inst_subs_given                       false
% 3.71/1.00  --inst_orphan_elimination               true
% 3.71/1.00  --inst_learning_loop_flag               true
% 3.71/1.00  --inst_learning_start                   3000
% 3.71/1.00  --inst_learning_factor                  2
% 3.71/1.00  --inst_start_prop_sim_after_learn       3
% 3.71/1.00  --inst_sel_renew                        solver
% 3.71/1.00  --inst_lit_activity_flag                true
% 3.71/1.00  --inst_restr_to_given                   false
% 3.71/1.00  --inst_activity_threshold               500
% 3.71/1.00  --inst_out_proof                        true
% 3.71/1.00  
% 3.71/1.00  ------ Resolution Options
% 3.71/1.00  
% 3.71/1.00  --resolution_flag                       true
% 3.71/1.00  --res_lit_sel                           adaptive
% 3.71/1.00  --res_lit_sel_side                      none
% 3.71/1.00  --res_ordering                          kbo
% 3.71/1.00  --res_to_prop_solver                    active
% 3.71/1.00  --res_prop_simpl_new                    false
% 3.71/1.00  --res_prop_simpl_given                  true
% 3.71/1.00  --res_passive_queue_type                priority_queues
% 3.71/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.71/1.00  --res_passive_queues_freq               [15;5]
% 3.71/1.00  --res_forward_subs                      full
% 3.71/1.00  --res_backward_subs                     full
% 3.71/1.00  --res_forward_subs_resolution           true
% 3.71/1.00  --res_backward_subs_resolution          true
% 3.71/1.00  --res_orphan_elimination                true
% 3.71/1.00  --res_time_limit                        2.
% 3.71/1.00  --res_out_proof                         true
% 3.71/1.00  
% 3.71/1.00  ------ Superposition Options
% 3.71/1.00  
% 3.71/1.00  --superposition_flag                    true
% 3.71/1.00  --sup_passive_queue_type                priority_queues
% 3.71/1.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.71/1.00  --sup_passive_queues_freq               [1;4]
% 3.71/1.00  --demod_completeness_check              fast
% 3.71/1.00  --demod_use_ground                      true
% 3.71/1.00  --sup_to_prop_solver                    passive
% 3.71/1.00  --sup_prop_simpl_new                    true
% 3.71/1.00  --sup_prop_simpl_given                  true
% 3.71/1.00  --sup_fun_splitting                     false
% 3.71/1.00  --sup_smt_interval                      50000
% 3.71/1.00  
% 3.71/1.00  ------ Superposition Simplification Setup
% 3.71/1.00  
% 3.71/1.00  --sup_indices_passive                   []
% 3.71/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.71/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/1.00  --sup_full_bw                           [BwDemod]
% 3.71/1.00  --sup_immed_triv                        [TrivRules]
% 3.71/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/1.00  --sup_immed_bw_main                     []
% 3.71/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.71/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/1.00  
% 3.71/1.00  ------ Combination Options
% 3.71/1.00  
% 3.71/1.00  --comb_res_mult                         3
% 3.71/1.00  --comb_sup_mult                         2
% 3.71/1.00  --comb_inst_mult                        10
% 3.71/1.00  
% 3.71/1.00  ------ Debug Options
% 3.71/1.00  
% 3.71/1.00  --dbg_backtrace                         false
% 3.71/1.00  --dbg_dump_prop_clauses                 false
% 3.71/1.00  --dbg_dump_prop_clauses_file            -
% 3.71/1.00  --dbg_out_stat                          false
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  ------ Proving...
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  % SZS status Theorem for theBenchmark.p
% 3.71/1.00  
% 3.71/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.71/1.00  
% 3.71/1.00  fof(f11,axiom,(
% 3.71/1.00    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = k1_xboole_0) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f16,plain,(
% 3.71/1.00    ! [X0] : ? [X1] : (k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.71/1.00    inference(pure_predicate_removal,[],[f11])).
% 3.71/1.00  
% 3.71/1.00  fof(f18,plain,(
% 3.71/1.00    ! [X0] : ? [X1] : (k1_relat_1(X1) = X0 & v1_relat_1(X1))),
% 3.71/1.00    inference(pure_predicate_removal,[],[f16])).
% 3.71/1.00  
% 3.71/1.00  fof(f31,plain,(
% 3.71/1.00    ! [X0] : (? [X1] : (k1_relat_1(X1) = X0 & v1_relat_1(X1)) => (k1_relat_1(sK1(X0)) = X0 & v1_relat_1(sK1(X0))))),
% 3.71/1.00    introduced(choice_axiom,[])).
% 3.71/1.00  
% 3.71/1.00  fof(f32,plain,(
% 3.71/1.00    ! [X0] : (k1_relat_1(sK1(X0)) = X0 & v1_relat_1(sK1(X0)))),
% 3.71/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f31])).
% 3.71/1.00  
% 3.71/1.00  fof(f46,plain,(
% 3.71/1.00    ( ! [X0] : (v1_relat_1(sK1(X0))) )),
% 3.71/1.00    inference(cnf_transformation,[],[f32])).
% 3.71/1.00  
% 3.71/1.00  fof(f12,conjecture,(
% 3.71/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 3.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f13,negated_conjecture,(
% 3.71/1.00    ~! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 3.71/1.00    inference(negated_conjecture,[],[f12])).
% 3.71/1.00  
% 3.71/1.00  fof(f28,plain,(
% 3.71/1.00    ? [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) != k10_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(X2))),
% 3.71/1.00    inference(ennf_transformation,[],[f13])).
% 3.71/1.00  
% 3.71/1.00  fof(f33,plain,(
% 3.71/1.00    ? [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) != k10_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(X2)) => (k3_xboole_0(sK2,k10_relat_1(sK4,sK3)) != k10_relat_1(k7_relat_1(sK4,sK2),sK3) & v1_relat_1(sK4))),
% 3.71/1.00    introduced(choice_axiom,[])).
% 3.71/1.00  
% 3.71/1.00  fof(f34,plain,(
% 3.71/1.00    k3_xboole_0(sK2,k10_relat_1(sK4,sK3)) != k10_relat_1(k7_relat_1(sK4,sK2),sK3) & v1_relat_1(sK4)),
% 3.71/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f33])).
% 3.71/1.00  
% 3.71/1.00  fof(f48,plain,(
% 3.71/1.00    v1_relat_1(sK4)),
% 3.71/1.00    inference(cnf_transformation,[],[f34])).
% 3.71/1.00  
% 3.71/1.00  fof(f5,axiom,(
% 3.71/1.00    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f22,plain,(
% 3.71/1.00    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.71/1.00    inference(ennf_transformation,[],[f5])).
% 3.71/1.00  
% 3.71/1.00  fof(f39,plain,(
% 3.71/1.00    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f22])).
% 3.71/1.00  
% 3.71/1.00  fof(f7,axiom,(
% 3.71/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 3.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f24,plain,(
% 3.71/1.00    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.71/1.00    inference(ennf_transformation,[],[f7])).
% 3.71/1.00  
% 3.71/1.00  fof(f41,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f24])).
% 3.71/1.00  
% 3.71/1.00  fof(f4,axiom,(
% 3.71/1.00    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f20,plain,(
% 3.71/1.00    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.71/1.00    inference(ennf_transformation,[],[f4])).
% 3.71/1.00  
% 3.71/1.00  fof(f21,plain,(
% 3.71/1.00    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.71/1.00    inference(flattening,[],[f20])).
% 3.71/1.00  
% 3.71/1.00  fof(f38,plain,(
% 3.71/1.00    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f21])).
% 3.71/1.00  
% 3.71/1.00  fof(f9,axiom,(
% 3.71/1.00    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 3.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f27,plain,(
% 3.71/1.00    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.71/1.00    inference(ennf_transformation,[],[f9])).
% 3.71/1.00  
% 3.71/1.00  fof(f43,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f27])).
% 3.71/1.00  
% 3.71/1.00  fof(f47,plain,(
% 3.71/1.00    ( ! [X0] : (k1_relat_1(sK1(X0)) = X0) )),
% 3.71/1.00    inference(cnf_transformation,[],[f32])).
% 3.71/1.00  
% 3.71/1.00  fof(f6,axiom,(
% 3.71/1.00    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)))),
% 3.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f23,plain,(
% 3.71/1.00    ! [X0,X1] : (! [X2] : (k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.71/1.00    inference(ennf_transformation,[],[f6])).
% 3.71/1.00  
% 3.71/1.00  fof(f40,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f23])).
% 3.71/1.00  
% 3.71/1.00  fof(f49,plain,(
% 3.71/1.00    k3_xboole_0(sK2,k10_relat_1(sK4,sK3)) != k10_relat_1(k7_relat_1(sK4,sK2),sK3)),
% 3.71/1.00    inference(cnf_transformation,[],[f34])).
% 3.71/1.00  
% 3.71/1.00  fof(f1,axiom,(
% 3.71/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f35,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f1])).
% 3.71/1.00  
% 3.71/1.00  cnf(c_12,plain,
% 3.71/1.00      ( v1_relat_1(sK1(X0)) ),
% 3.71/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_251,plain,
% 3.71/1.00      ( v1_relat_1(sK1(X0)) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_14,negated_conjecture,
% 3.71/1.00      ( v1_relat_1(sK4) ),
% 3.71/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_250,plain,
% 3.71/1.00      ( v1_relat_1(sK4) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4,plain,
% 3.71/1.00      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 3.71/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_257,plain,
% 3.71/1.00      ( v1_relat_1(X0) != iProver_top
% 3.71/1.00      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6,plain,
% 3.71/1.00      ( ~ v1_relat_1(X0)
% 3.71/1.00      | ~ v1_relat_1(X1)
% 3.71/1.00      | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
% 3.71/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_255,plain,
% 3.71/1.00      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 3.71/1.00      | v1_relat_1(X1) != iProver_top
% 3.71/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1018,plain,
% 3.71/1.00      ( k10_relat_1(k7_relat_1(X0,X1),k1_relat_1(X2)) = k1_relat_1(k5_relat_1(k7_relat_1(X0,X1),X2))
% 3.71/1.00      | v1_relat_1(X0) != iProver_top
% 3.71/1.00      | v1_relat_1(X2) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_257,c_255]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4207,plain,
% 3.71/1.00      ( k10_relat_1(k7_relat_1(sK4,X0),k1_relat_1(X1)) = k1_relat_1(k5_relat_1(k7_relat_1(sK4,X0),X1))
% 3.71/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_250,c_1018]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_11889,plain,
% 3.71/1.00      ( k10_relat_1(k7_relat_1(sK4,X0),k1_relat_1(sK1(X1))) = k1_relat_1(k5_relat_1(k7_relat_1(sK4,X0),sK1(X1))) ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_251,c_4207]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3,plain,
% 3.71/1.00      ( ~ v1_relat_1(X0)
% 3.71/1.00      | ~ v1_relat_1(X1)
% 3.71/1.00      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 3.71/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_258,plain,
% 3.71/1.00      ( v1_relat_1(X0) != iProver_top
% 3.71/1.00      | v1_relat_1(X1) != iProver_top
% 3.71/1.00      | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_8,plain,
% 3.71/1.00      ( ~ v1_relat_1(X0)
% 3.71/1.00      | k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1) ),
% 3.71/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_253,plain,
% 3.71/1.00      ( k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1)
% 3.71/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_852,plain,
% 3.71/1.00      ( k1_relat_1(k7_relat_1(k5_relat_1(X0,X1),X2)) = k3_xboole_0(k1_relat_1(k5_relat_1(X0,X1)),X2)
% 3.71/1.00      | v1_relat_1(X1) != iProver_top
% 3.71/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_258,c_253]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1692,plain,
% 3.71/1.00      ( k1_relat_1(k7_relat_1(k5_relat_1(sK4,X0),X1)) = k3_xboole_0(k1_relat_1(k5_relat_1(sK4,X0)),X1)
% 3.71/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_250,c_852]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_10781,plain,
% 3.71/1.00      ( k1_relat_1(k7_relat_1(k5_relat_1(sK4,sK1(X0)),X1)) = k3_xboole_0(k1_relat_1(k5_relat_1(sK4,sK1(X0))),X1) ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_251,c_1692]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1021,plain,
% 3.71/1.00      ( k10_relat_1(sK4,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK4,X0))
% 3.71/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_250,c_255]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_5679,plain,
% 3.71/1.00      ( k10_relat_1(sK4,k1_relat_1(sK1(X0))) = k1_relat_1(k5_relat_1(sK4,sK1(X0))) ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_251,c_1021]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_11,plain,
% 3.71/1.00      ( k1_relat_1(sK1(X0)) = X0 ),
% 3.71/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_5684,plain,
% 3.71/1.00      ( k1_relat_1(k5_relat_1(sK4,sK1(X0))) = k10_relat_1(sK4,X0) ),
% 3.71/1.00      inference(light_normalisation,[status(thm)],[c_5679,c_11]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_5,plain,
% 3.71/1.00      ( ~ v1_relat_1(X0)
% 3.71/1.00      | ~ v1_relat_1(X1)
% 3.71/1.00      | k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1) ),
% 3.71/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_256,plain,
% 3.71/1.00      ( k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1)
% 3.71/1.00      | v1_relat_1(X0) != iProver_top
% 3.71/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1069,plain,
% 3.71/1.00      ( k7_relat_1(k5_relat_1(sK4,X0),X1) = k5_relat_1(k7_relat_1(sK4,X1),X0)
% 3.71/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_250,c_256]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_7537,plain,
% 3.71/1.00      ( k7_relat_1(k5_relat_1(sK4,sK1(X0)),X1) = k5_relat_1(k7_relat_1(sK4,X1),sK1(X0)) ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_251,c_1069]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_10810,plain,
% 3.71/1.00      ( k1_relat_1(k5_relat_1(k7_relat_1(sK4,X0),sK1(X1))) = k3_xboole_0(k10_relat_1(sK4,X1),X0) ),
% 3.71/1.00      inference(light_normalisation,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_10781,c_5684,c_7537]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_11919,plain,
% 3.71/1.00      ( k10_relat_1(k7_relat_1(sK4,X0),k1_relat_1(sK1(X1))) = k3_xboole_0(k10_relat_1(sK4,X1),X0) ),
% 3.71/1.00      inference(light_normalisation,[status(thm)],[c_11889,c_10810]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_11920,plain,
% 3.71/1.00      ( k10_relat_1(k7_relat_1(sK4,X0),X1) = k3_xboole_0(k10_relat_1(sK4,X1),X0) ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_11919,c_11]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_13,negated_conjecture,
% 3.71/1.00      ( k3_xboole_0(sK2,k10_relat_1(sK4,sK3)) != k10_relat_1(k7_relat_1(sK4,sK2),sK3) ),
% 3.71/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_11954,plain,
% 3.71/1.00      ( k3_xboole_0(k10_relat_1(sK4,sK3),sK2) != k3_xboole_0(sK2,k10_relat_1(sK4,sK3)) ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_11920,c_13]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_0,plain,
% 3.71/1.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_5625,plain,
% 3.71/1.00      ( k3_xboole_0(k10_relat_1(sK4,sK3),sK2) = k3_xboole_0(sK2,k10_relat_1(sK4,sK3)) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(contradiction,plain,
% 3.71/1.00      ( $false ),
% 3.71/1.00      inference(minisat,[status(thm)],[c_11954,c_5625]) ).
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.71/1.00  
% 3.71/1.00  ------                               Statistics
% 3.71/1.00  
% 3.71/1.00  ------ Selected
% 3.71/1.00  
% 3.71/1.00  total_time:                             0.396
% 3.71/1.00  
%------------------------------------------------------------------------------
