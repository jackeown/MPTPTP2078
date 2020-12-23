%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:15 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 140 expanded)
%              Number of clauses        :   40 (  48 expanded)
%              Number of leaves         :   13 (  35 expanded)
%              Depth                    :   18
%              Number of atoms          :  123 ( 216 expanded)
%              Number of equality atoms :   72 ( 120 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f27,f40,f40])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f40])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,X2)
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    & r1_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f24])).

fof(f43,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f11,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f42,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f41,f40])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f8,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f35,f40])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f29,f40])).

fof(f44,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_93,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_16,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_168,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK1 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_93,c_16])).

cnf(c_169,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_168])).

cnf(c_884,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_169])).

cnf(c_13,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1019,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_884,c_13])).

cnf(c_12,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1035,plain,
    ( k4_xboole_0(sK2,sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_1019,c_12])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_445,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_446,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_447,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1479,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,X2)
    | r1_tarski(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_446,c_447])).

cnf(c_12365,plain,
    ( k2_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK0)) = k4_xboole_0(X0,sK0) ),
    inference(superposition,[status(thm)],[c_445,c_1479])).

cnf(c_12955,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_1035,c_12365])).

cnf(c_14,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_996,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_14,c_0])).

cnf(c_11,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2918,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_996,c_11])).

cnf(c_3422,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_2918,c_0])).

cnf(c_12990,plain,
    ( k4_xboole_0(sK2,sK0) = sK2 ),
    inference(demodulation,[status(thm)],[c_12955,c_3422])).

cnf(c_908,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_13])).

cnf(c_13590,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK2,sK2)) = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_12990,c_908])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_461,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9,c_12])).

cnf(c_13678,plain,
    ( k4_xboole_0(sK0,sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_13590,c_12,c_461])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_91,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_15,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_163,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | sK2 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_91,c_15])).

cnf(c_164,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_163])).

cnf(c_14068,plain,
    ( k4_xboole_0(sK0,sK0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13678,c_164])).

cnf(c_14069,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14068,c_461])).

cnf(c_14070,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_14069])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:46:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.72/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.02  
% 3.72/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.72/1.02  
% 3.72/1.02  ------  iProver source info
% 3.72/1.02  
% 3.72/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.72/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.72/1.02  git: non_committed_changes: false
% 3.72/1.02  git: last_make_outside_of_git: false
% 3.72/1.02  
% 3.72/1.02  ------ 
% 3.72/1.02  
% 3.72/1.02  ------ Input Options
% 3.72/1.02  
% 3.72/1.02  --out_options                           all
% 3.72/1.02  --tptp_safe_out                         true
% 3.72/1.02  --problem_path                          ""
% 3.72/1.02  --include_path                          ""
% 3.72/1.02  --clausifier                            res/vclausify_rel
% 3.72/1.02  --clausifier_options                    --mode clausify
% 3.72/1.02  --stdin                                 false
% 3.72/1.02  --stats_out                             all
% 3.72/1.02  
% 3.72/1.02  ------ General Options
% 3.72/1.02  
% 3.72/1.02  --fof                                   false
% 3.72/1.02  --time_out_real                         305.
% 3.72/1.02  --time_out_virtual                      -1.
% 3.72/1.02  --symbol_type_check                     false
% 3.72/1.02  --clausify_out                          false
% 3.72/1.02  --sig_cnt_out                           false
% 3.72/1.02  --trig_cnt_out                          false
% 3.72/1.02  --trig_cnt_out_tolerance                1.
% 3.72/1.02  --trig_cnt_out_sk_spl                   false
% 3.72/1.02  --abstr_cl_out                          false
% 3.72/1.02  
% 3.72/1.02  ------ Global Options
% 3.72/1.02  
% 3.72/1.02  --schedule                              default
% 3.72/1.02  --add_important_lit                     false
% 3.72/1.02  --prop_solver_per_cl                    1000
% 3.72/1.02  --min_unsat_core                        false
% 3.72/1.02  --soft_assumptions                      false
% 3.72/1.02  --soft_lemma_size                       3
% 3.72/1.02  --prop_impl_unit_size                   0
% 3.72/1.02  --prop_impl_unit                        []
% 3.72/1.02  --share_sel_clauses                     true
% 3.72/1.02  --reset_solvers                         false
% 3.72/1.02  --bc_imp_inh                            [conj_cone]
% 3.72/1.02  --conj_cone_tolerance                   3.
% 3.72/1.02  --extra_neg_conj                        none
% 3.72/1.02  --large_theory_mode                     true
% 3.72/1.02  --prolific_symb_bound                   200
% 3.72/1.02  --lt_threshold                          2000
% 3.72/1.02  --clause_weak_htbl                      true
% 3.72/1.02  --gc_record_bc_elim                     false
% 3.72/1.02  
% 3.72/1.02  ------ Preprocessing Options
% 3.72/1.02  
% 3.72/1.02  --preprocessing_flag                    true
% 3.72/1.02  --time_out_prep_mult                    0.1
% 3.72/1.02  --splitting_mode                        input
% 3.72/1.02  --splitting_grd                         true
% 3.72/1.02  --splitting_cvd                         false
% 3.72/1.02  --splitting_cvd_svl                     false
% 3.72/1.02  --splitting_nvd                         32
% 3.72/1.02  --sub_typing                            true
% 3.72/1.02  --prep_gs_sim                           true
% 3.72/1.02  --prep_unflatten                        true
% 3.72/1.02  --prep_res_sim                          true
% 3.72/1.02  --prep_upred                            true
% 3.72/1.02  --prep_sem_filter                       exhaustive
% 3.72/1.02  --prep_sem_filter_out                   false
% 3.72/1.02  --pred_elim                             true
% 3.72/1.02  --res_sim_input                         true
% 3.72/1.02  --eq_ax_congr_red                       true
% 3.72/1.02  --pure_diseq_elim                       true
% 3.72/1.02  --brand_transform                       false
% 3.72/1.02  --non_eq_to_eq                          false
% 3.72/1.02  --prep_def_merge                        true
% 3.72/1.02  --prep_def_merge_prop_impl              false
% 3.72/1.02  --prep_def_merge_mbd                    true
% 3.72/1.02  --prep_def_merge_tr_red                 false
% 3.72/1.02  --prep_def_merge_tr_cl                  false
% 3.72/1.02  --smt_preprocessing                     true
% 3.72/1.02  --smt_ac_axioms                         fast
% 3.72/1.02  --preprocessed_out                      false
% 3.72/1.02  --preprocessed_stats                    false
% 3.72/1.02  
% 3.72/1.02  ------ Abstraction refinement Options
% 3.72/1.02  
% 3.72/1.02  --abstr_ref                             []
% 3.72/1.02  --abstr_ref_prep                        false
% 3.72/1.02  --abstr_ref_until_sat                   false
% 3.72/1.02  --abstr_ref_sig_restrict                funpre
% 3.72/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.72/1.02  --abstr_ref_under                       []
% 3.72/1.02  
% 3.72/1.02  ------ SAT Options
% 3.72/1.02  
% 3.72/1.02  --sat_mode                              false
% 3.72/1.02  --sat_fm_restart_options                ""
% 3.72/1.02  --sat_gr_def                            false
% 3.72/1.02  --sat_epr_types                         true
% 3.72/1.02  --sat_non_cyclic_types                  false
% 3.72/1.02  --sat_finite_models                     false
% 3.72/1.02  --sat_fm_lemmas                         false
% 3.72/1.02  --sat_fm_prep                           false
% 3.72/1.02  --sat_fm_uc_incr                        true
% 3.72/1.02  --sat_out_model                         small
% 3.72/1.02  --sat_out_clauses                       false
% 3.72/1.02  
% 3.72/1.02  ------ QBF Options
% 3.72/1.02  
% 3.72/1.02  --qbf_mode                              false
% 3.72/1.02  --qbf_elim_univ                         false
% 3.72/1.02  --qbf_dom_inst                          none
% 3.72/1.02  --qbf_dom_pre_inst                      false
% 3.72/1.02  --qbf_sk_in                             false
% 3.72/1.02  --qbf_pred_elim                         true
% 3.72/1.02  --qbf_split                             512
% 3.72/1.02  
% 3.72/1.02  ------ BMC1 Options
% 3.72/1.02  
% 3.72/1.02  --bmc1_incremental                      false
% 3.72/1.02  --bmc1_axioms                           reachable_all
% 3.72/1.02  --bmc1_min_bound                        0
% 3.72/1.02  --bmc1_max_bound                        -1
% 3.72/1.02  --bmc1_max_bound_default                -1
% 3.72/1.02  --bmc1_symbol_reachability              true
% 3.72/1.02  --bmc1_property_lemmas                  false
% 3.72/1.02  --bmc1_k_induction                      false
% 3.72/1.02  --bmc1_non_equiv_states                 false
% 3.72/1.02  --bmc1_deadlock                         false
% 3.72/1.02  --bmc1_ucm                              false
% 3.72/1.02  --bmc1_add_unsat_core                   none
% 3.72/1.02  --bmc1_unsat_core_children              false
% 3.72/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.72/1.02  --bmc1_out_stat                         full
% 3.72/1.02  --bmc1_ground_init                      false
% 3.72/1.02  --bmc1_pre_inst_next_state              false
% 3.72/1.02  --bmc1_pre_inst_state                   false
% 3.72/1.02  --bmc1_pre_inst_reach_state             false
% 3.72/1.02  --bmc1_out_unsat_core                   false
% 3.72/1.02  --bmc1_aig_witness_out                  false
% 3.72/1.02  --bmc1_verbose                          false
% 3.72/1.02  --bmc1_dump_clauses_tptp                false
% 3.72/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.72/1.02  --bmc1_dump_file                        -
% 3.72/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.72/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.72/1.02  --bmc1_ucm_extend_mode                  1
% 3.72/1.02  --bmc1_ucm_init_mode                    2
% 3.72/1.02  --bmc1_ucm_cone_mode                    none
% 3.72/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.72/1.02  --bmc1_ucm_relax_model                  4
% 3.72/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.72/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.72/1.02  --bmc1_ucm_layered_model                none
% 3.72/1.02  --bmc1_ucm_max_lemma_size               10
% 3.72/1.02  
% 3.72/1.02  ------ AIG Options
% 3.72/1.02  
% 3.72/1.02  --aig_mode                              false
% 3.72/1.02  
% 3.72/1.02  ------ Instantiation Options
% 3.72/1.02  
% 3.72/1.02  --instantiation_flag                    true
% 3.72/1.02  --inst_sos_flag                         false
% 3.72/1.02  --inst_sos_phase                        true
% 3.72/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.72/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.72/1.02  --inst_lit_sel_side                     num_symb
% 3.72/1.02  --inst_solver_per_active                1400
% 3.72/1.02  --inst_solver_calls_frac                1.
% 3.72/1.02  --inst_passive_queue_type               priority_queues
% 3.72/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.72/1.02  --inst_passive_queues_freq              [25;2]
% 3.72/1.02  --inst_dismatching                      true
% 3.72/1.02  --inst_eager_unprocessed_to_passive     true
% 3.72/1.02  --inst_prop_sim_given                   true
% 3.72/1.02  --inst_prop_sim_new                     false
% 3.72/1.02  --inst_subs_new                         false
% 3.72/1.02  --inst_eq_res_simp                      false
% 3.72/1.02  --inst_subs_given                       false
% 3.72/1.02  --inst_orphan_elimination               true
% 3.72/1.02  --inst_learning_loop_flag               true
% 3.72/1.02  --inst_learning_start                   3000
% 3.72/1.02  --inst_learning_factor                  2
% 3.72/1.02  --inst_start_prop_sim_after_learn       3
% 3.72/1.02  --inst_sel_renew                        solver
% 3.72/1.02  --inst_lit_activity_flag                true
% 3.72/1.02  --inst_restr_to_given                   false
% 3.72/1.02  --inst_activity_threshold               500
% 3.72/1.02  --inst_out_proof                        true
% 3.72/1.02  
% 3.72/1.02  ------ Resolution Options
% 3.72/1.02  
% 3.72/1.02  --resolution_flag                       true
% 3.72/1.02  --res_lit_sel                           adaptive
% 3.72/1.02  --res_lit_sel_side                      none
% 3.72/1.02  --res_ordering                          kbo
% 3.72/1.02  --res_to_prop_solver                    active
% 3.72/1.02  --res_prop_simpl_new                    false
% 3.72/1.02  --res_prop_simpl_given                  true
% 3.72/1.02  --res_passive_queue_type                priority_queues
% 3.72/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.72/1.02  --res_passive_queues_freq               [15;5]
% 3.72/1.02  --res_forward_subs                      full
% 3.72/1.02  --res_backward_subs                     full
% 3.72/1.02  --res_forward_subs_resolution           true
% 3.72/1.02  --res_backward_subs_resolution          true
% 3.72/1.02  --res_orphan_elimination                true
% 3.72/1.02  --res_time_limit                        2.
% 3.72/1.02  --res_out_proof                         true
% 3.72/1.02  
% 3.72/1.02  ------ Superposition Options
% 3.72/1.02  
% 3.72/1.02  --superposition_flag                    true
% 3.72/1.02  --sup_passive_queue_type                priority_queues
% 3.72/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.72/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.72/1.02  --demod_completeness_check              fast
% 3.72/1.02  --demod_use_ground                      true
% 3.72/1.02  --sup_to_prop_solver                    passive
% 3.72/1.02  --sup_prop_simpl_new                    true
% 3.72/1.02  --sup_prop_simpl_given                  true
% 3.72/1.02  --sup_fun_splitting                     false
% 3.72/1.02  --sup_smt_interval                      50000
% 3.72/1.02  
% 3.72/1.02  ------ Superposition Simplification Setup
% 3.72/1.02  
% 3.72/1.02  --sup_indices_passive                   []
% 3.72/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.72/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/1.02  --sup_full_bw                           [BwDemod]
% 3.72/1.02  --sup_immed_triv                        [TrivRules]
% 3.72/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.72/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/1.02  --sup_immed_bw_main                     []
% 3.72/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.72/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/1.02  
% 3.72/1.02  ------ Combination Options
% 3.72/1.02  
% 3.72/1.02  --comb_res_mult                         3
% 3.72/1.02  --comb_sup_mult                         2
% 3.72/1.02  --comb_inst_mult                        10
% 3.72/1.02  
% 3.72/1.02  ------ Debug Options
% 3.72/1.02  
% 3.72/1.02  --dbg_backtrace                         false
% 3.72/1.02  --dbg_dump_prop_clauses                 false
% 3.72/1.02  --dbg_dump_prop_clauses_file            -
% 3.72/1.02  --dbg_out_stat                          false
% 3.72/1.02  ------ Parsing...
% 3.72/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.72/1.02  
% 3.72/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.72/1.02  
% 3.72/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.72/1.02  
% 3.72/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.72/1.02  ------ Proving...
% 3.72/1.02  ------ Problem Properties 
% 3.72/1.02  
% 3.72/1.02  
% 3.72/1.02  clauses                                 17
% 3.72/1.02  conjectures                             1
% 3.72/1.02  EPR                                     2
% 3.72/1.02  Horn                                    17
% 3.72/1.02  unary                                   12
% 3.72/1.02  binary                                  5
% 3.72/1.02  lits                                    22
% 3.72/1.02  lits eq                                 14
% 3.72/1.02  fd_pure                                 0
% 3.72/1.02  fd_pseudo                               0
% 3.72/1.02  fd_cond                                 0
% 3.72/1.02  fd_pseudo_cond                          0
% 3.72/1.02  AC symbols                              0
% 3.72/1.02  
% 3.72/1.02  ------ Schedule dynamic 5 is on 
% 3.72/1.02  
% 3.72/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.72/1.02  
% 3.72/1.02  
% 3.72/1.02  ------ 
% 3.72/1.02  Current options:
% 3.72/1.02  ------ 
% 3.72/1.02  
% 3.72/1.02  ------ Input Options
% 3.72/1.02  
% 3.72/1.02  --out_options                           all
% 3.72/1.02  --tptp_safe_out                         true
% 3.72/1.02  --problem_path                          ""
% 3.72/1.02  --include_path                          ""
% 3.72/1.02  --clausifier                            res/vclausify_rel
% 3.72/1.02  --clausifier_options                    --mode clausify
% 3.72/1.02  --stdin                                 false
% 3.72/1.02  --stats_out                             all
% 3.72/1.02  
% 3.72/1.02  ------ General Options
% 3.72/1.02  
% 3.72/1.02  --fof                                   false
% 3.72/1.02  --time_out_real                         305.
% 3.72/1.02  --time_out_virtual                      -1.
% 3.72/1.02  --symbol_type_check                     false
% 3.72/1.02  --clausify_out                          false
% 3.72/1.02  --sig_cnt_out                           false
% 3.72/1.02  --trig_cnt_out                          false
% 3.72/1.02  --trig_cnt_out_tolerance                1.
% 3.72/1.02  --trig_cnt_out_sk_spl                   false
% 3.72/1.02  --abstr_cl_out                          false
% 3.72/1.02  
% 3.72/1.02  ------ Global Options
% 3.72/1.02  
% 3.72/1.02  --schedule                              default
% 3.72/1.02  --add_important_lit                     false
% 3.72/1.02  --prop_solver_per_cl                    1000
% 3.72/1.02  --min_unsat_core                        false
% 3.72/1.02  --soft_assumptions                      false
% 3.72/1.02  --soft_lemma_size                       3
% 3.72/1.02  --prop_impl_unit_size                   0
% 3.72/1.02  --prop_impl_unit                        []
% 3.72/1.02  --share_sel_clauses                     true
% 3.72/1.02  --reset_solvers                         false
% 3.72/1.02  --bc_imp_inh                            [conj_cone]
% 3.72/1.02  --conj_cone_tolerance                   3.
% 3.72/1.02  --extra_neg_conj                        none
% 3.72/1.02  --large_theory_mode                     true
% 3.72/1.02  --prolific_symb_bound                   200
% 3.72/1.02  --lt_threshold                          2000
% 3.72/1.02  --clause_weak_htbl                      true
% 3.72/1.02  --gc_record_bc_elim                     false
% 3.72/1.02  
% 3.72/1.02  ------ Preprocessing Options
% 3.72/1.02  
% 3.72/1.02  --preprocessing_flag                    true
% 3.72/1.02  --time_out_prep_mult                    0.1
% 3.72/1.02  --splitting_mode                        input
% 3.72/1.02  --splitting_grd                         true
% 3.72/1.02  --splitting_cvd                         false
% 3.72/1.02  --splitting_cvd_svl                     false
% 3.72/1.02  --splitting_nvd                         32
% 3.72/1.02  --sub_typing                            true
% 3.72/1.02  --prep_gs_sim                           true
% 3.72/1.02  --prep_unflatten                        true
% 3.72/1.02  --prep_res_sim                          true
% 3.72/1.02  --prep_upred                            true
% 3.72/1.02  --prep_sem_filter                       exhaustive
% 3.72/1.02  --prep_sem_filter_out                   false
% 3.72/1.02  --pred_elim                             true
% 3.72/1.02  --res_sim_input                         true
% 3.72/1.02  --eq_ax_congr_red                       true
% 3.72/1.02  --pure_diseq_elim                       true
% 3.72/1.02  --brand_transform                       false
% 3.72/1.02  --non_eq_to_eq                          false
% 3.72/1.02  --prep_def_merge                        true
% 3.72/1.02  --prep_def_merge_prop_impl              false
% 3.72/1.02  --prep_def_merge_mbd                    true
% 3.72/1.02  --prep_def_merge_tr_red                 false
% 3.72/1.02  --prep_def_merge_tr_cl                  false
% 3.72/1.02  --smt_preprocessing                     true
% 3.72/1.02  --smt_ac_axioms                         fast
% 3.72/1.02  --preprocessed_out                      false
% 3.72/1.02  --preprocessed_stats                    false
% 3.72/1.02  
% 3.72/1.02  ------ Abstraction refinement Options
% 3.72/1.02  
% 3.72/1.02  --abstr_ref                             []
% 3.72/1.02  --abstr_ref_prep                        false
% 3.72/1.02  --abstr_ref_until_sat                   false
% 3.72/1.02  --abstr_ref_sig_restrict                funpre
% 3.72/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.72/1.02  --abstr_ref_under                       []
% 3.72/1.02  
% 3.72/1.02  ------ SAT Options
% 3.72/1.02  
% 3.72/1.02  --sat_mode                              false
% 3.72/1.02  --sat_fm_restart_options                ""
% 3.72/1.02  --sat_gr_def                            false
% 3.72/1.02  --sat_epr_types                         true
% 3.72/1.02  --sat_non_cyclic_types                  false
% 3.72/1.02  --sat_finite_models                     false
% 3.72/1.02  --sat_fm_lemmas                         false
% 3.72/1.02  --sat_fm_prep                           false
% 3.72/1.02  --sat_fm_uc_incr                        true
% 3.72/1.02  --sat_out_model                         small
% 3.72/1.02  --sat_out_clauses                       false
% 3.72/1.02  
% 3.72/1.02  ------ QBF Options
% 3.72/1.02  
% 3.72/1.02  --qbf_mode                              false
% 3.72/1.02  --qbf_elim_univ                         false
% 3.72/1.02  --qbf_dom_inst                          none
% 3.72/1.02  --qbf_dom_pre_inst                      false
% 3.72/1.02  --qbf_sk_in                             false
% 3.72/1.02  --qbf_pred_elim                         true
% 3.72/1.02  --qbf_split                             512
% 3.72/1.02  
% 3.72/1.02  ------ BMC1 Options
% 3.72/1.02  
% 3.72/1.02  --bmc1_incremental                      false
% 3.72/1.02  --bmc1_axioms                           reachable_all
% 3.72/1.02  --bmc1_min_bound                        0
% 3.72/1.02  --bmc1_max_bound                        -1
% 3.72/1.02  --bmc1_max_bound_default                -1
% 3.72/1.02  --bmc1_symbol_reachability              true
% 3.72/1.02  --bmc1_property_lemmas                  false
% 3.72/1.02  --bmc1_k_induction                      false
% 3.72/1.02  --bmc1_non_equiv_states                 false
% 3.72/1.02  --bmc1_deadlock                         false
% 3.72/1.02  --bmc1_ucm                              false
% 3.72/1.02  --bmc1_add_unsat_core                   none
% 3.72/1.02  --bmc1_unsat_core_children              false
% 3.72/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.72/1.02  --bmc1_out_stat                         full
% 3.72/1.02  --bmc1_ground_init                      false
% 3.72/1.02  --bmc1_pre_inst_next_state              false
% 3.72/1.02  --bmc1_pre_inst_state                   false
% 3.72/1.02  --bmc1_pre_inst_reach_state             false
% 3.72/1.02  --bmc1_out_unsat_core                   false
% 3.72/1.02  --bmc1_aig_witness_out                  false
% 3.72/1.02  --bmc1_verbose                          false
% 3.72/1.02  --bmc1_dump_clauses_tptp                false
% 3.72/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.72/1.02  --bmc1_dump_file                        -
% 3.72/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.72/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.72/1.02  --bmc1_ucm_extend_mode                  1
% 3.72/1.02  --bmc1_ucm_init_mode                    2
% 3.72/1.02  --bmc1_ucm_cone_mode                    none
% 3.72/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.72/1.02  --bmc1_ucm_relax_model                  4
% 3.72/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.72/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.72/1.02  --bmc1_ucm_layered_model                none
% 3.72/1.02  --bmc1_ucm_max_lemma_size               10
% 3.72/1.02  
% 3.72/1.02  ------ AIG Options
% 3.72/1.02  
% 3.72/1.02  --aig_mode                              false
% 3.72/1.02  
% 3.72/1.02  ------ Instantiation Options
% 3.72/1.02  
% 3.72/1.02  --instantiation_flag                    true
% 3.72/1.02  --inst_sos_flag                         false
% 3.72/1.02  --inst_sos_phase                        true
% 3.72/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.72/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.72/1.02  --inst_lit_sel_side                     none
% 3.72/1.02  --inst_solver_per_active                1400
% 3.72/1.02  --inst_solver_calls_frac                1.
% 3.72/1.02  --inst_passive_queue_type               priority_queues
% 3.72/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.72/1.02  --inst_passive_queues_freq              [25;2]
% 3.72/1.02  --inst_dismatching                      true
% 3.72/1.02  --inst_eager_unprocessed_to_passive     true
% 3.72/1.02  --inst_prop_sim_given                   true
% 3.72/1.02  --inst_prop_sim_new                     false
% 3.72/1.02  --inst_subs_new                         false
% 3.72/1.02  --inst_eq_res_simp                      false
% 3.72/1.02  --inst_subs_given                       false
% 3.72/1.02  --inst_orphan_elimination               true
% 3.72/1.02  --inst_learning_loop_flag               true
% 3.72/1.02  --inst_learning_start                   3000
% 3.72/1.02  --inst_learning_factor                  2
% 3.72/1.02  --inst_start_prop_sim_after_learn       3
% 3.72/1.02  --inst_sel_renew                        solver
% 3.72/1.02  --inst_lit_activity_flag                true
% 3.72/1.02  --inst_restr_to_given                   false
% 3.72/1.02  --inst_activity_threshold               500
% 3.72/1.02  --inst_out_proof                        true
% 3.72/1.02  
% 3.72/1.02  ------ Resolution Options
% 3.72/1.02  
% 3.72/1.02  --resolution_flag                       false
% 3.72/1.02  --res_lit_sel                           adaptive
% 3.72/1.02  --res_lit_sel_side                      none
% 3.72/1.02  --res_ordering                          kbo
% 3.72/1.02  --res_to_prop_solver                    active
% 3.72/1.02  --res_prop_simpl_new                    false
% 3.72/1.02  --res_prop_simpl_given                  true
% 3.72/1.02  --res_passive_queue_type                priority_queues
% 3.72/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.72/1.02  --res_passive_queues_freq               [15;5]
% 3.72/1.02  --res_forward_subs                      full
% 3.72/1.02  --res_backward_subs                     full
% 3.72/1.02  --res_forward_subs_resolution           true
% 3.72/1.02  --res_backward_subs_resolution          true
% 3.72/1.02  --res_orphan_elimination                true
% 3.72/1.02  --res_time_limit                        2.
% 3.72/1.02  --res_out_proof                         true
% 3.72/1.02  
% 3.72/1.02  ------ Superposition Options
% 3.72/1.02  
% 3.72/1.02  --superposition_flag                    true
% 3.72/1.02  --sup_passive_queue_type                priority_queues
% 3.72/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.72/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.72/1.02  --demod_completeness_check              fast
% 3.72/1.02  --demod_use_ground                      true
% 3.72/1.02  --sup_to_prop_solver                    passive
% 3.72/1.02  --sup_prop_simpl_new                    true
% 3.72/1.02  --sup_prop_simpl_given                  true
% 3.72/1.02  --sup_fun_splitting                     false
% 3.72/1.02  --sup_smt_interval                      50000
% 3.72/1.02  
% 3.72/1.02  ------ Superposition Simplification Setup
% 3.72/1.02  
% 3.72/1.02  --sup_indices_passive                   []
% 3.72/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.72/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/1.02  --sup_full_bw                           [BwDemod]
% 3.72/1.02  --sup_immed_triv                        [TrivRules]
% 3.72/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.72/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/1.02  --sup_immed_bw_main                     []
% 3.72/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.72/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/1.02  
% 3.72/1.02  ------ Combination Options
% 3.72/1.02  
% 3.72/1.02  --comb_res_mult                         3
% 3.72/1.02  --comb_sup_mult                         2
% 3.72/1.02  --comb_inst_mult                        10
% 3.72/1.02  
% 3.72/1.02  ------ Debug Options
% 3.72/1.02  
% 3.72/1.02  --dbg_backtrace                         false
% 3.72/1.02  --dbg_dump_prop_clauses                 false
% 3.72/1.02  --dbg_dump_prop_clauses_file            -
% 3.72/1.02  --dbg_out_stat                          false
% 3.72/1.02  
% 3.72/1.02  
% 3.72/1.02  
% 3.72/1.02  
% 3.72/1.02  ------ Proving...
% 3.72/1.02  
% 3.72/1.02  
% 3.72/1.02  % SZS status Theorem for theBenchmark.p
% 3.72/1.02  
% 3.72/1.02   Resolution empty clause
% 3.72/1.02  
% 3.72/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.72/1.02  
% 3.72/1.02  fof(f2,axiom,(
% 3.72/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.72/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.02  
% 3.72/1.02  fof(f27,plain,(
% 3.72/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.72/1.02    inference(cnf_transformation,[],[f2])).
% 3.72/1.02  
% 3.72/1.02  fof(f13,axiom,(
% 3.72/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.72/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.02  
% 3.72/1.02  fof(f40,plain,(
% 3.72/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.72/1.02    inference(cnf_transformation,[],[f13])).
% 3.72/1.02  
% 3.72/1.02  fof(f45,plain,(
% 3.72/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.72/1.02    inference(definition_unfolding,[],[f27,f40,f40])).
% 3.72/1.02  
% 3.72/1.02  fof(f3,axiom,(
% 3.72/1.02    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.72/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.02  
% 3.72/1.02  fof(f22,plain,(
% 3.72/1.02    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.72/1.02    inference(nnf_transformation,[],[f3])).
% 3.72/1.02  
% 3.72/1.02  fof(f28,plain,(
% 3.72/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.72/1.02    inference(cnf_transformation,[],[f22])).
% 3.72/1.02  
% 3.72/1.02  fof(f47,plain,(
% 3.72/1.02    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.72/1.02    inference(definition_unfolding,[],[f28,f40])).
% 3.72/1.02  
% 3.72/1.02  fof(f15,conjecture,(
% 3.72/1.02    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 3.72/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.02  
% 3.72/1.02  fof(f16,negated_conjecture,(
% 3.72/1.02    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 3.72/1.02    inference(negated_conjecture,[],[f15])).
% 3.72/1.02  
% 3.72/1.02  fof(f20,plain,(
% 3.72/1.02    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & (r1_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 3.72/1.02    inference(ennf_transformation,[],[f16])).
% 3.72/1.02  
% 3.72/1.02  fof(f21,plain,(
% 3.72/1.02    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 3.72/1.02    inference(flattening,[],[f20])).
% 3.72/1.02  
% 3.72/1.02  fof(f24,plain,(
% 3.72/1.02    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 3.72/1.02    introduced(choice_axiom,[])).
% 3.72/1.02  
% 3.72/1.02  fof(f25,plain,(
% 3.72/1.02    ~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 3.72/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f24])).
% 3.72/1.02  
% 3.72/1.02  fof(f43,plain,(
% 3.72/1.02    r1_xboole_0(sK1,sK2)),
% 3.72/1.02    inference(cnf_transformation,[],[f25])).
% 3.72/1.02  
% 3.72/1.02  fof(f12,axiom,(
% 3.72/1.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.72/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.02  
% 3.72/1.02  fof(f39,plain,(
% 3.72/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.72/1.02    inference(cnf_transformation,[],[f12])).
% 3.72/1.02  
% 3.72/1.02  fof(f49,plain,(
% 3.72/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.72/1.02    inference(definition_unfolding,[],[f39,f40])).
% 3.72/1.02  
% 3.72/1.02  fof(f11,axiom,(
% 3.72/1.02    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.72/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.02  
% 3.72/1.02  fof(f38,plain,(
% 3.72/1.02    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.72/1.02    inference(cnf_transformation,[],[f11])).
% 3.72/1.02  
% 3.72/1.02  fof(f42,plain,(
% 3.72/1.02    r1_tarski(sK0,sK1)),
% 3.72/1.02    inference(cnf_transformation,[],[f25])).
% 3.72/1.02  
% 3.72/1.02  fof(f9,axiom,(
% 3.72/1.02    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 3.72/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.02  
% 3.72/1.02  fof(f19,plain,(
% 3.72/1.02    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 3.72/1.02    inference(ennf_transformation,[],[f9])).
% 3.72/1.02  
% 3.72/1.02  fof(f36,plain,(
% 3.72/1.02    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 3.72/1.02    inference(cnf_transformation,[],[f19])).
% 3.72/1.02  
% 3.72/1.02  fof(f6,axiom,(
% 3.72/1.02    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.72/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.02  
% 3.72/1.02  fof(f18,plain,(
% 3.72/1.02    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.72/1.02    inference(ennf_transformation,[],[f6])).
% 3.72/1.02  
% 3.72/1.02  fof(f33,plain,(
% 3.72/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.72/1.02    inference(cnf_transformation,[],[f18])).
% 3.72/1.02  
% 3.72/1.02  fof(f14,axiom,(
% 3.72/1.02    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 3.72/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.02  
% 3.72/1.02  fof(f41,plain,(
% 3.72/1.02    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 3.72/1.02    inference(cnf_transformation,[],[f14])).
% 3.72/1.02  
% 3.72/1.02  fof(f50,plain,(
% 3.72/1.02    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 3.72/1.02    inference(definition_unfolding,[],[f41,f40])).
% 3.72/1.02  
% 3.72/1.02  fof(f1,axiom,(
% 3.72/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.72/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.02  
% 3.72/1.02  fof(f26,plain,(
% 3.72/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.72/1.02    inference(cnf_transformation,[],[f1])).
% 3.72/1.02  
% 3.72/1.02  fof(f10,axiom,(
% 3.72/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.72/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.02  
% 3.72/1.02  fof(f37,plain,(
% 3.72/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.72/1.02    inference(cnf_transformation,[],[f10])).
% 3.72/1.02  
% 3.72/1.02  fof(f8,axiom,(
% 3.72/1.02    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.72/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.72/1.02  
% 3.72/1.02  fof(f35,plain,(
% 3.72/1.02    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.72/1.02    inference(cnf_transformation,[],[f8])).
% 3.72/1.02  
% 3.72/1.02  fof(f48,plain,(
% 3.72/1.02    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 3.72/1.02    inference(definition_unfolding,[],[f35,f40])).
% 3.72/1.02  
% 3.72/1.02  fof(f29,plain,(
% 3.72/1.02    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.72/1.02    inference(cnf_transformation,[],[f22])).
% 3.72/1.02  
% 3.72/1.02  fof(f46,plain,(
% 3.72/1.02    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.72/1.02    inference(definition_unfolding,[],[f29,f40])).
% 3.72/1.02  
% 3.72/1.02  fof(f44,plain,(
% 3.72/1.02    ~r1_xboole_0(sK0,sK2)),
% 3.72/1.02    inference(cnf_transformation,[],[f25])).
% 3.72/1.02  
% 3.72/1.02  cnf(c_1,plain,
% 3.72/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.72/1.02      inference(cnf_transformation,[],[f45]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_3,plain,
% 3.72/1.02      ( ~ r1_xboole_0(X0,X1)
% 3.72/1.02      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.72/1.02      inference(cnf_transformation,[],[f47]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_93,plain,
% 3.72/1.02      ( ~ r1_xboole_0(X0,X1)
% 3.72/1.02      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.72/1.02      inference(prop_impl,[status(thm)],[c_3]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_16,negated_conjecture,
% 3.72/1.02      ( r1_xboole_0(sK1,sK2) ),
% 3.72/1.02      inference(cnf_transformation,[],[f43]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_168,plain,
% 3.72/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 3.72/1.02      | sK1 != X0
% 3.72/1.02      | sK2 != X1 ),
% 3.72/1.02      inference(resolution_lifted,[status(thm)],[c_93,c_16]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_169,plain,
% 3.72/1.02      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 3.72/1.02      inference(unflattening,[status(thm)],[c_168]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_884,plain,
% 3.72/1.02      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k1_xboole_0 ),
% 3.72/1.02      inference(superposition,[status(thm)],[c_1,c_169]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_13,plain,
% 3.72/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.72/1.02      inference(cnf_transformation,[],[f49]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_1019,plain,
% 3.72/1.02      ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK1) ),
% 3.72/1.02      inference(superposition,[status(thm)],[c_884,c_13]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_12,plain,
% 3.72/1.02      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.72/1.02      inference(cnf_transformation,[],[f38]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_1035,plain,
% 3.72/1.02      ( k4_xboole_0(sK2,sK1) = sK2 ),
% 3.72/1.02      inference(demodulation,[status(thm)],[c_1019,c_12]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_17,negated_conjecture,
% 3.72/1.02      ( r1_tarski(sK0,sK1) ),
% 3.72/1.02      inference(cnf_transformation,[],[f42]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_445,plain,
% 3.72/1.02      ( r1_tarski(sK0,sK1) = iProver_top ),
% 3.72/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_10,plain,
% 3.72/1.02      ( ~ r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ),
% 3.72/1.02      inference(cnf_transformation,[],[f36]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_446,plain,
% 3.72/1.02      ( r1_tarski(X0,X1) != iProver_top
% 3.72/1.02      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) = iProver_top ),
% 3.72/1.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_7,plain,
% 3.72/1.02      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 3.72/1.02      inference(cnf_transformation,[],[f33]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_447,plain,
% 3.72/1.02      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 3.72/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_1479,plain,
% 3.72/1.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,X2)
% 3.72/1.02      | r1_tarski(X2,X1) != iProver_top ),
% 3.72/1.02      inference(superposition,[status(thm)],[c_446,c_447]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_12365,plain,
% 3.72/1.02      ( k2_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK0)) = k4_xboole_0(X0,sK0) ),
% 3.72/1.02      inference(superposition,[status(thm)],[c_445,c_1479]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_12955,plain,
% 3.72/1.02      ( k2_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k4_xboole_0(sK2,sK0) ),
% 3.72/1.02      inference(superposition,[status(thm)],[c_1035,c_12365]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_14,plain,
% 3.72/1.02      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 3.72/1.02      inference(cnf_transformation,[],[f50]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_0,plain,
% 3.72/1.02      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 3.72/1.02      inference(cnf_transformation,[],[f26]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_996,plain,
% 3.72/1.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 3.72/1.02      inference(superposition,[status(thm)],[c_14,c_0]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_11,plain,
% 3.72/1.02      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 3.72/1.02      inference(cnf_transformation,[],[f37]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_2918,plain,
% 3.72/1.02      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 3.72/1.02      inference(superposition,[status(thm)],[c_996,c_11]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_3422,plain,
% 3.72/1.02      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 3.72/1.02      inference(superposition,[status(thm)],[c_2918,c_0]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_12990,plain,
% 3.72/1.02      ( k4_xboole_0(sK2,sK0) = sK2 ),
% 3.72/1.02      inference(demodulation,[status(thm)],[c_12955,c_3422]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_908,plain,
% 3.72/1.02      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 3.72/1.02      inference(superposition,[status(thm)],[c_1,c_13]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_13590,plain,
% 3.72/1.02      ( k4_xboole_0(sK0,k4_xboole_0(sK2,sK2)) = k4_xboole_0(sK0,sK2) ),
% 3.72/1.02      inference(superposition,[status(thm)],[c_12990,c_908]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_9,plain,
% 3.72/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.72/1.02      inference(cnf_transformation,[],[f48]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_461,plain,
% 3.72/1.02      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.72/1.02      inference(light_normalisation,[status(thm)],[c_9,c_12]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_13678,plain,
% 3.72/1.02      ( k4_xboole_0(sK0,sK2) = sK0 ),
% 3.72/1.02      inference(demodulation,[status(thm)],[c_13590,c_12,c_461]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_2,plain,
% 3.72/1.02      ( r1_xboole_0(X0,X1)
% 3.72/1.02      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 3.72/1.02      inference(cnf_transformation,[],[f46]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_91,plain,
% 3.72/1.02      ( r1_xboole_0(X0,X1)
% 3.72/1.02      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 3.72/1.02      inference(prop_impl,[status(thm)],[c_2]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_15,negated_conjecture,
% 3.72/1.02      ( ~ r1_xboole_0(sK0,sK2) ),
% 3.72/1.02      inference(cnf_transformation,[],[f44]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_163,plain,
% 3.72/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 3.72/1.02      | sK2 != X1
% 3.72/1.02      | sK0 != X0 ),
% 3.72/1.02      inference(resolution_lifted,[status(thm)],[c_91,c_15]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_164,plain,
% 3.72/1.02      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k1_xboole_0 ),
% 3.72/1.02      inference(unflattening,[status(thm)],[c_163]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_14068,plain,
% 3.72/1.02      ( k4_xboole_0(sK0,sK0) != k1_xboole_0 ),
% 3.72/1.02      inference(demodulation,[status(thm)],[c_13678,c_164]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_14069,plain,
% 3.72/1.02      ( k1_xboole_0 != k1_xboole_0 ),
% 3.72/1.02      inference(demodulation,[status(thm)],[c_14068,c_461]) ).
% 3.72/1.02  
% 3.72/1.02  cnf(c_14070,plain,
% 3.72/1.02      ( $false ),
% 3.72/1.02      inference(equality_resolution_simp,[status(thm)],[c_14069]) ).
% 3.72/1.02  
% 3.72/1.02  
% 3.72/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.72/1.02  
% 3.72/1.02  ------                               Statistics
% 3.72/1.02  
% 3.72/1.02  ------ General
% 3.72/1.02  
% 3.72/1.02  abstr_ref_over_cycles:                  0
% 3.72/1.02  abstr_ref_under_cycles:                 0
% 3.72/1.02  gc_basic_clause_elim:                   0
% 3.72/1.02  forced_gc_time:                         0
% 3.72/1.02  parsing_time:                           0.009
% 3.72/1.02  unif_index_cands_time:                  0.
% 3.72/1.02  unif_index_add_time:                    0.
% 3.72/1.02  orderings_time:                         0.
% 3.72/1.02  out_proof_time:                         0.006
% 3.72/1.02  total_time:                             0.4
% 3.72/1.02  num_of_symbols:                         39
% 3.72/1.02  num_of_terms:                           14778
% 3.72/1.02  
% 3.72/1.02  ------ Preprocessing
% 3.72/1.02  
% 3.72/1.02  num_of_splits:                          0
% 3.72/1.02  num_of_split_atoms:                     0
% 3.72/1.02  num_of_reused_defs:                     0
% 3.72/1.02  num_eq_ax_congr_red:                    1
% 3.72/1.02  num_of_sem_filtered_clauses:            1
% 3.72/1.02  num_of_subtypes:                        0
% 3.72/1.02  monotx_restored_types:                  0
% 3.72/1.02  sat_num_of_epr_types:                   0
% 3.72/1.02  sat_num_of_non_cyclic_types:            0
% 3.72/1.02  sat_guarded_non_collapsed_types:        0
% 3.72/1.02  num_pure_diseq_elim:                    0
% 3.72/1.02  simp_replaced_by:                       0
% 3.72/1.02  res_preprocessed:                       80
% 3.72/1.02  prep_upred:                             0
% 3.72/1.02  prep_unflattend:                        4
% 3.72/1.02  smt_new_axioms:                         0
% 3.72/1.02  pred_elim_cands:                        1
% 3.72/1.02  pred_elim:                              1
% 3.72/1.02  pred_elim_cl:                           1
% 3.72/1.02  pred_elim_cycles:                       3
% 3.72/1.02  merged_defs:                            10
% 3.72/1.02  merged_defs_ncl:                        0
% 3.72/1.02  bin_hyper_res:                          10
% 3.72/1.02  prep_cycles:                            4
% 3.72/1.02  pred_elim_time:                         0.
% 3.72/1.02  splitting_time:                         0.
% 3.72/1.02  sem_filter_time:                        0.
% 3.72/1.02  monotx_time:                            0.
% 3.72/1.02  subtype_inf_time:                       0.
% 3.72/1.02  
% 3.72/1.02  ------ Problem properties
% 3.72/1.02  
% 3.72/1.02  clauses:                                17
% 3.72/1.02  conjectures:                            1
% 3.72/1.02  epr:                                    2
% 3.72/1.02  horn:                                   17
% 3.72/1.02  ground:                                 4
% 3.72/1.02  unary:                                  12
% 3.72/1.02  binary:                                 5
% 3.72/1.02  lits:                                   22
% 3.72/1.02  lits_eq:                                14
% 3.72/1.02  fd_pure:                                0
% 3.72/1.02  fd_pseudo:                              0
% 3.72/1.02  fd_cond:                                0
% 3.72/1.02  fd_pseudo_cond:                         0
% 3.72/1.02  ac_symbols:                             0
% 3.72/1.02  
% 3.72/1.02  ------ Propositional Solver
% 3.72/1.02  
% 3.72/1.02  prop_solver_calls:                      31
% 3.72/1.02  prop_fast_solver_calls:                 568
% 3.72/1.02  smt_solver_calls:                       0
% 3.72/1.02  smt_fast_solver_calls:                  0
% 3.72/1.02  prop_num_of_clauses:                    6092
% 3.72/1.02  prop_preprocess_simplified:             11129
% 3.72/1.02  prop_fo_subsumed:                       17
% 3.72/1.02  prop_solver_time:                       0.
% 3.72/1.02  smt_solver_time:                        0.
% 3.72/1.02  smt_fast_solver_time:                   0.
% 3.72/1.02  prop_fast_solver_time:                  0.
% 3.72/1.02  prop_unsat_core_time:                   0.
% 3.72/1.02  
% 3.72/1.02  ------ QBF
% 3.72/1.02  
% 3.72/1.02  qbf_q_res:                              0
% 3.72/1.02  qbf_num_tautologies:                    0
% 3.72/1.02  qbf_prep_cycles:                        0
% 3.72/1.02  
% 3.72/1.02  ------ BMC1
% 3.72/1.02  
% 3.72/1.02  bmc1_current_bound:                     -1
% 3.72/1.02  bmc1_last_solved_bound:                 -1
% 3.72/1.02  bmc1_unsat_core_size:                   -1
% 3.72/1.02  bmc1_unsat_core_parents_size:           -1
% 3.72/1.02  bmc1_merge_next_fun:                    0
% 3.72/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.72/1.02  
% 3.72/1.02  ------ Instantiation
% 3.72/1.02  
% 3.72/1.02  inst_num_of_clauses:                    2459
% 3.72/1.02  inst_num_in_passive:                    859
% 3.72/1.02  inst_num_in_active:                     807
% 3.72/1.02  inst_num_in_unprocessed:                793
% 3.72/1.02  inst_num_of_loops:                      810
% 3.72/1.02  inst_num_of_learning_restarts:          0
% 3.72/1.02  inst_num_moves_active_passive:          1
% 3.72/1.02  inst_lit_activity:                      0
% 3.72/1.02  inst_lit_activity_moves:                0
% 3.72/1.02  inst_num_tautologies:                   0
% 3.72/1.02  inst_num_prop_implied:                  0
% 3.72/1.02  inst_num_existing_simplified:           0
% 3.72/1.02  inst_num_eq_res_simplified:             0
% 3.72/1.02  inst_num_child_elim:                    0
% 3.72/1.02  inst_num_of_dismatching_blockings:      348
% 3.72/1.02  inst_num_of_non_proper_insts:           1661
% 3.72/1.02  inst_num_of_duplicates:                 0
% 3.72/1.02  inst_inst_num_from_inst_to_res:         0
% 3.72/1.02  inst_dismatching_checking_time:         0.
% 3.72/1.02  
% 3.72/1.02  ------ Resolution
% 3.72/1.02  
% 3.72/1.02  res_num_of_clauses:                     0
% 3.72/1.02  res_num_in_passive:                     0
% 3.72/1.02  res_num_in_active:                      0
% 3.72/1.02  res_num_of_loops:                       84
% 3.72/1.02  res_forward_subset_subsumed:            161
% 3.72/1.02  res_backward_subset_subsumed:           0
% 3.72/1.02  res_forward_subsumed:                   0
% 3.72/1.02  res_backward_subsumed:                  0
% 3.72/1.02  res_forward_subsumption_resolution:     0
% 3.72/1.02  res_backward_subsumption_resolution:    0
% 3.72/1.02  res_clause_to_clause_subsumption:       2709
% 3.72/1.02  res_orphan_elimination:                 0
% 3.72/1.02  res_tautology_del:                      171
% 3.72/1.02  res_num_eq_res_simplified:              1
% 3.72/1.02  res_num_sel_changes:                    0
% 3.72/1.02  res_moves_from_active_to_pass:          0
% 3.72/1.02  
% 3.72/1.02  ------ Superposition
% 3.72/1.02  
% 3.72/1.02  sup_time_total:                         0.
% 3.72/1.02  sup_time_generating:                    0.
% 3.72/1.02  sup_time_sim_full:                      0.
% 3.72/1.02  sup_time_sim_immed:                     0.
% 3.72/1.02  
% 3.72/1.02  sup_num_of_clauses:                     419
% 3.72/1.02  sup_num_in_active:                      141
% 3.72/1.02  sup_num_in_passive:                     278
% 3.72/1.02  sup_num_of_loops:                       160
% 3.72/1.02  sup_fw_superposition:                   1082
% 3.72/1.02  sup_bw_superposition:                   428
% 3.72/1.02  sup_immediate_simplified:               661
% 3.72/1.02  sup_given_eliminated:                   2
% 3.72/1.02  comparisons_done:                       0
% 3.72/1.02  comparisons_avoided:                    0
% 3.72/1.02  
% 3.72/1.02  ------ Simplifications
% 3.72/1.02  
% 3.72/1.02  
% 3.72/1.02  sim_fw_subset_subsumed:                 67
% 3.72/1.02  sim_bw_subset_subsumed:                 16
% 3.72/1.02  sim_fw_subsumed:                        117
% 3.72/1.02  sim_bw_subsumed:                        14
% 3.72/1.02  sim_fw_subsumption_res:                 0
% 3.72/1.02  sim_bw_subsumption_res:                 0
% 3.72/1.02  sim_tautology_del:                      82
% 3.72/1.02  sim_eq_tautology_del:                   108
% 3.72/1.02  sim_eq_res_simp:                        5
% 3.72/1.02  sim_fw_demodulated:                     357
% 3.72/1.02  sim_bw_demodulated:                     17
% 3.72/1.02  sim_light_normalised:                   238
% 3.72/1.02  sim_joinable_taut:                      0
% 3.72/1.02  sim_joinable_simp:                      0
% 3.72/1.02  sim_ac_normalised:                      0
% 3.72/1.02  sim_smt_subsumption:                    0
% 3.72/1.02  
%------------------------------------------------------------------------------
