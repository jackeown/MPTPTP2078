%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:09 EST 2020

% Result     : Theorem 43.67s
% Output     : CNFRefutation 43.67s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 153 expanded)
%              Number of clauses        :   26 (  31 expanded)
%              Number of leaves         :    9 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  108 ( 244 expanded)
%              Number of equality atoms :   42 ( 117 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1))
      & k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f36])).

fof(f48,plain,(
    ! [X2,X0,X1] : k3_tarski(k1_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) = k2_zfmisc_1(k3_tarski(k1_enumset1(X0,X0,X1)),X2) ),
    inference(definition_unfolding,[],[f38,f43,f43])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f35,f36,f36])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f34,f43])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f20,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f21,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f20])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f21,f24])).

fof(f41,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X2,X0,X1] : k3_tarski(k1_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(X2,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f39,f43,f43])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),k3_tarski(k1_enumset1(X1,X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f43,f43])).

fof(f42,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,(
    ~ r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) ),
    inference(definition_unfolding,[],[f42,f43,f43,f43])).

cnf(c_11,plain,
    ( k3_tarski(k1_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(k3_tarski(k1_enumset1(X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_9,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_8,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_357,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_743,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_357])).

cnf(c_857,plain,
    ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k3_tarski(k1_enumset1(X2,X2,X0)),X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_743])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_355,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_359,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1711,plain,
    ( r1_tarski(k2_zfmisc_1(sK4,sK5),X0) != iProver_top
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_355,c_359])).

cnf(c_2209,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(X0,X0,sK4)),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_857,c_1711])).

cnf(c_855,plain,
    ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k3_tarski(k1_enumset1(X0,X0,X2)),X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_357])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_354,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1712,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK3),X0) != iProver_top
    | r1_tarski(sK0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_354,c_359])).

cnf(c_2234,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,X0)),sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_855,c_1712])).

cnf(c_10,plain,
    ( k3_tarski(k1_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))) = k2_zfmisc_1(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),k3_tarski(k1_enumset1(X1,X1,X3))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_360,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X3) != iProver_top
    | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),k3_tarski(k1_enumset1(X1,X1,X3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3024,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(X3,k2_zfmisc_1(X1,X4)) != iProver_top
    | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X3)),k2_zfmisc_1(X1,k3_tarski(k1_enumset1(X2,X2,X4)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_360])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_356,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_163199,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK5)) != iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3024,c_356])).

cnf(c_165116,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2234,c_163199])).

cnf(c_165730,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2209,c_165116])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:45:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 43.67/6.05  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.67/6.05  
% 43.67/6.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.67/6.05  
% 43.67/6.05  ------  iProver source info
% 43.67/6.05  
% 43.67/6.05  git: date: 2020-06-30 10:37:57 +0100
% 43.67/6.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.67/6.05  git: non_committed_changes: false
% 43.67/6.05  git: last_make_outside_of_git: false
% 43.67/6.05  
% 43.67/6.05  ------ 
% 43.67/6.05  
% 43.67/6.05  ------ Input Options
% 43.67/6.05  
% 43.67/6.05  --out_options                           all
% 43.67/6.05  --tptp_safe_out                         true
% 43.67/6.05  --problem_path                          ""
% 43.67/6.05  --include_path                          ""
% 43.67/6.05  --clausifier                            res/vclausify_rel
% 43.67/6.05  --clausifier_options                    ""
% 43.67/6.05  --stdin                                 false
% 43.67/6.05  --stats_out                             all
% 43.67/6.05  
% 43.67/6.05  ------ General Options
% 43.67/6.05  
% 43.67/6.05  --fof                                   false
% 43.67/6.05  --time_out_real                         305.
% 43.67/6.05  --time_out_virtual                      -1.
% 43.67/6.05  --symbol_type_check                     false
% 43.67/6.05  --clausify_out                          false
% 43.67/6.05  --sig_cnt_out                           false
% 43.67/6.05  --trig_cnt_out                          false
% 43.67/6.05  --trig_cnt_out_tolerance                1.
% 43.67/6.05  --trig_cnt_out_sk_spl                   false
% 43.67/6.05  --abstr_cl_out                          false
% 43.67/6.05  
% 43.67/6.05  ------ Global Options
% 43.67/6.05  
% 43.67/6.05  --schedule                              default
% 43.67/6.05  --add_important_lit                     false
% 43.67/6.05  --prop_solver_per_cl                    1000
% 43.67/6.05  --min_unsat_core                        false
% 43.67/6.05  --soft_assumptions                      false
% 43.67/6.05  --soft_lemma_size                       3
% 43.67/6.05  --prop_impl_unit_size                   0
% 43.67/6.05  --prop_impl_unit                        []
% 43.67/6.05  --share_sel_clauses                     true
% 43.67/6.05  --reset_solvers                         false
% 43.67/6.05  --bc_imp_inh                            [conj_cone]
% 43.67/6.05  --conj_cone_tolerance                   3.
% 43.67/6.05  --extra_neg_conj                        none
% 43.67/6.05  --large_theory_mode                     true
% 43.67/6.05  --prolific_symb_bound                   200
% 43.67/6.05  --lt_threshold                          2000
% 43.67/6.05  --clause_weak_htbl                      true
% 43.67/6.05  --gc_record_bc_elim                     false
% 43.67/6.05  
% 43.67/6.05  ------ Preprocessing Options
% 43.67/6.05  
% 43.67/6.05  --preprocessing_flag                    true
% 43.67/6.05  --time_out_prep_mult                    0.1
% 43.67/6.05  --splitting_mode                        input
% 43.67/6.05  --splitting_grd                         true
% 43.67/6.05  --splitting_cvd                         false
% 43.67/6.05  --splitting_cvd_svl                     false
% 43.67/6.05  --splitting_nvd                         32
% 43.67/6.05  --sub_typing                            true
% 43.67/6.05  --prep_gs_sim                           true
% 43.67/6.05  --prep_unflatten                        true
% 43.67/6.05  --prep_res_sim                          true
% 43.67/6.05  --prep_upred                            true
% 43.67/6.05  --prep_sem_filter                       exhaustive
% 43.67/6.05  --prep_sem_filter_out                   false
% 43.67/6.05  --pred_elim                             true
% 43.67/6.05  --res_sim_input                         true
% 43.67/6.05  --eq_ax_congr_red                       true
% 43.67/6.05  --pure_diseq_elim                       true
% 43.67/6.05  --brand_transform                       false
% 43.67/6.05  --non_eq_to_eq                          false
% 43.67/6.05  --prep_def_merge                        true
% 43.67/6.05  --prep_def_merge_prop_impl              false
% 43.67/6.05  --prep_def_merge_mbd                    true
% 43.67/6.05  --prep_def_merge_tr_red                 false
% 43.67/6.05  --prep_def_merge_tr_cl                  false
% 43.67/6.05  --smt_preprocessing                     true
% 43.67/6.05  --smt_ac_axioms                         fast
% 43.67/6.05  --preprocessed_out                      false
% 43.67/6.05  --preprocessed_stats                    false
% 43.67/6.05  
% 43.67/6.05  ------ Abstraction refinement Options
% 43.67/6.05  
% 43.67/6.05  --abstr_ref                             []
% 43.67/6.05  --abstr_ref_prep                        false
% 43.67/6.05  --abstr_ref_until_sat                   false
% 43.67/6.05  --abstr_ref_sig_restrict                funpre
% 43.67/6.05  --abstr_ref_af_restrict_to_split_sk     false
% 43.67/6.05  --abstr_ref_under                       []
% 43.67/6.05  
% 43.67/6.05  ------ SAT Options
% 43.67/6.05  
% 43.67/6.05  --sat_mode                              false
% 43.67/6.05  --sat_fm_restart_options                ""
% 43.67/6.05  --sat_gr_def                            false
% 43.67/6.05  --sat_epr_types                         true
% 43.67/6.05  --sat_non_cyclic_types                  false
% 43.67/6.05  --sat_finite_models                     false
% 43.67/6.05  --sat_fm_lemmas                         false
% 43.67/6.05  --sat_fm_prep                           false
% 43.67/6.05  --sat_fm_uc_incr                        true
% 43.67/6.05  --sat_out_model                         small
% 43.67/6.05  --sat_out_clauses                       false
% 43.67/6.05  
% 43.67/6.05  ------ QBF Options
% 43.67/6.05  
% 43.67/6.05  --qbf_mode                              false
% 43.67/6.05  --qbf_elim_univ                         false
% 43.67/6.05  --qbf_dom_inst                          none
% 43.67/6.05  --qbf_dom_pre_inst                      false
% 43.67/6.05  --qbf_sk_in                             false
% 43.67/6.05  --qbf_pred_elim                         true
% 43.67/6.05  --qbf_split                             512
% 43.67/6.05  
% 43.67/6.05  ------ BMC1 Options
% 43.67/6.05  
% 43.67/6.05  --bmc1_incremental                      false
% 43.67/6.05  --bmc1_axioms                           reachable_all
% 43.67/6.05  --bmc1_min_bound                        0
% 43.67/6.05  --bmc1_max_bound                        -1
% 43.67/6.05  --bmc1_max_bound_default                -1
% 43.67/6.05  --bmc1_symbol_reachability              true
% 43.67/6.05  --bmc1_property_lemmas                  false
% 43.67/6.05  --bmc1_k_induction                      false
% 43.67/6.05  --bmc1_non_equiv_states                 false
% 43.67/6.05  --bmc1_deadlock                         false
% 43.67/6.05  --bmc1_ucm                              false
% 43.67/6.05  --bmc1_add_unsat_core                   none
% 43.67/6.05  --bmc1_unsat_core_children              false
% 43.67/6.05  --bmc1_unsat_core_extrapolate_axioms    false
% 43.67/6.05  --bmc1_out_stat                         full
% 43.67/6.05  --bmc1_ground_init                      false
% 43.67/6.05  --bmc1_pre_inst_next_state              false
% 43.67/6.05  --bmc1_pre_inst_state                   false
% 43.67/6.05  --bmc1_pre_inst_reach_state             false
% 43.67/6.05  --bmc1_out_unsat_core                   false
% 43.67/6.05  --bmc1_aig_witness_out                  false
% 43.67/6.05  --bmc1_verbose                          false
% 43.67/6.05  --bmc1_dump_clauses_tptp                false
% 43.67/6.05  --bmc1_dump_unsat_core_tptp             false
% 43.67/6.05  --bmc1_dump_file                        -
% 43.67/6.05  --bmc1_ucm_expand_uc_limit              128
% 43.67/6.05  --bmc1_ucm_n_expand_iterations          6
% 43.67/6.05  --bmc1_ucm_extend_mode                  1
% 43.67/6.05  --bmc1_ucm_init_mode                    2
% 43.67/6.05  --bmc1_ucm_cone_mode                    none
% 43.67/6.05  --bmc1_ucm_reduced_relation_type        0
% 43.67/6.05  --bmc1_ucm_relax_model                  4
% 43.67/6.05  --bmc1_ucm_full_tr_after_sat            true
% 43.67/6.05  --bmc1_ucm_expand_neg_assumptions       false
% 43.67/6.05  --bmc1_ucm_layered_model                none
% 43.67/6.05  --bmc1_ucm_max_lemma_size               10
% 43.67/6.05  
% 43.67/6.05  ------ AIG Options
% 43.67/6.05  
% 43.67/6.05  --aig_mode                              false
% 43.67/6.05  
% 43.67/6.05  ------ Instantiation Options
% 43.67/6.05  
% 43.67/6.05  --instantiation_flag                    true
% 43.67/6.05  --inst_sos_flag                         true
% 43.67/6.05  --inst_sos_phase                        true
% 43.67/6.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.67/6.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.67/6.05  --inst_lit_sel_side                     num_symb
% 43.67/6.05  --inst_solver_per_active                1400
% 43.67/6.05  --inst_solver_calls_frac                1.
% 43.67/6.05  --inst_passive_queue_type               priority_queues
% 43.67/6.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.67/6.05  --inst_passive_queues_freq              [25;2]
% 43.67/6.05  --inst_dismatching                      true
% 43.67/6.05  --inst_eager_unprocessed_to_passive     true
% 43.67/6.05  --inst_prop_sim_given                   true
% 43.67/6.05  --inst_prop_sim_new                     false
% 43.67/6.05  --inst_subs_new                         false
% 43.67/6.05  --inst_eq_res_simp                      false
% 43.67/6.05  --inst_subs_given                       false
% 43.67/6.05  --inst_orphan_elimination               true
% 43.67/6.05  --inst_learning_loop_flag               true
% 43.67/6.05  --inst_learning_start                   3000
% 43.67/6.05  --inst_learning_factor                  2
% 43.67/6.05  --inst_start_prop_sim_after_learn       3
% 43.67/6.05  --inst_sel_renew                        solver
% 43.67/6.05  --inst_lit_activity_flag                true
% 43.67/6.05  --inst_restr_to_given                   false
% 43.67/6.05  --inst_activity_threshold               500
% 43.67/6.05  --inst_out_proof                        true
% 43.67/6.05  
% 43.67/6.05  ------ Resolution Options
% 43.67/6.05  
% 43.67/6.05  --resolution_flag                       true
% 43.67/6.05  --res_lit_sel                           adaptive
% 43.67/6.05  --res_lit_sel_side                      none
% 43.67/6.05  --res_ordering                          kbo
% 43.67/6.05  --res_to_prop_solver                    active
% 43.67/6.05  --res_prop_simpl_new                    false
% 43.67/6.05  --res_prop_simpl_given                  true
% 43.67/6.05  --res_passive_queue_type                priority_queues
% 43.67/6.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.67/6.05  --res_passive_queues_freq               [15;5]
% 43.67/6.05  --res_forward_subs                      full
% 43.67/6.05  --res_backward_subs                     full
% 43.67/6.05  --res_forward_subs_resolution           true
% 43.67/6.05  --res_backward_subs_resolution          true
% 43.67/6.05  --res_orphan_elimination                true
% 43.67/6.05  --res_time_limit                        2.
% 43.67/6.05  --res_out_proof                         true
% 43.67/6.05  
% 43.67/6.05  ------ Superposition Options
% 43.67/6.05  
% 43.67/6.05  --superposition_flag                    true
% 43.67/6.05  --sup_passive_queue_type                priority_queues
% 43.67/6.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.67/6.05  --sup_passive_queues_freq               [8;1;4]
% 43.67/6.05  --demod_completeness_check              fast
% 43.67/6.05  --demod_use_ground                      true
% 43.67/6.05  --sup_to_prop_solver                    passive
% 43.67/6.05  --sup_prop_simpl_new                    true
% 43.67/6.05  --sup_prop_simpl_given                  true
% 43.67/6.05  --sup_fun_splitting                     true
% 43.67/6.05  --sup_smt_interval                      50000
% 43.67/6.05  
% 43.67/6.05  ------ Superposition Simplification Setup
% 43.67/6.05  
% 43.67/6.05  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 43.67/6.05  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 43.67/6.05  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 43.67/6.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 43.67/6.05  --sup_full_triv                         [TrivRules;PropSubs]
% 43.67/6.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 43.67/6.05  --sup_full_bw                           [BwDemod;BwSubsumption]
% 43.67/6.05  --sup_immed_triv                        [TrivRules]
% 43.67/6.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.67/6.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.67/6.05  --sup_immed_bw_main                     []
% 43.67/6.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 43.67/6.05  --sup_input_triv                        [Unflattening;TrivRules]
% 43.67/6.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.67/6.05  --sup_input_bw                          []
% 43.67/6.05  
% 43.67/6.05  ------ Combination Options
% 43.67/6.05  
% 43.67/6.05  --comb_res_mult                         3
% 43.67/6.05  --comb_sup_mult                         2
% 43.67/6.05  --comb_inst_mult                        10
% 43.67/6.05  
% 43.67/6.05  ------ Debug Options
% 43.67/6.05  
% 43.67/6.05  --dbg_backtrace                         false
% 43.67/6.05  --dbg_dump_prop_clauses                 false
% 43.67/6.05  --dbg_dump_prop_clauses_file            -
% 43.67/6.05  --dbg_out_stat                          false
% 43.67/6.05  ------ Parsing...
% 43.67/6.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.67/6.05  
% 43.67/6.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 43.67/6.05  
% 43.67/6.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.67/6.05  
% 43.67/6.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.67/6.05  ------ Proving...
% 43.67/6.05  ------ Problem Properties 
% 43.67/6.05  
% 43.67/6.05  
% 43.67/6.05  clauses                                 14
% 43.67/6.05  conjectures                             3
% 43.67/6.05  EPR                                     3
% 43.67/6.05  Horn                                    14
% 43.67/6.05  unary                                   9
% 43.67/6.05  binary                                  2
% 43.67/6.05  lits                                    22
% 43.67/6.05  lits eq                                 6
% 43.67/6.05  fd_pure                                 0
% 43.67/6.05  fd_pseudo                               0
% 43.67/6.05  fd_cond                                 0
% 43.67/6.05  fd_pseudo_cond                          1
% 43.67/6.05  AC symbols                              0
% 43.67/6.05  
% 43.67/6.05  ------ Schedule dynamic 5 is on 
% 43.67/6.05  
% 43.67/6.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 43.67/6.05  
% 43.67/6.05  
% 43.67/6.05  ------ 
% 43.67/6.05  Current options:
% 43.67/6.05  ------ 
% 43.67/6.05  
% 43.67/6.05  ------ Input Options
% 43.67/6.05  
% 43.67/6.05  --out_options                           all
% 43.67/6.05  --tptp_safe_out                         true
% 43.67/6.05  --problem_path                          ""
% 43.67/6.05  --include_path                          ""
% 43.67/6.05  --clausifier                            res/vclausify_rel
% 43.67/6.05  --clausifier_options                    ""
% 43.67/6.05  --stdin                                 false
% 43.67/6.05  --stats_out                             all
% 43.67/6.05  
% 43.67/6.05  ------ General Options
% 43.67/6.05  
% 43.67/6.05  --fof                                   false
% 43.67/6.05  --time_out_real                         305.
% 43.67/6.05  --time_out_virtual                      -1.
% 43.67/6.05  --symbol_type_check                     false
% 43.67/6.05  --clausify_out                          false
% 43.67/6.05  --sig_cnt_out                           false
% 43.67/6.05  --trig_cnt_out                          false
% 43.67/6.05  --trig_cnt_out_tolerance                1.
% 43.67/6.05  --trig_cnt_out_sk_spl                   false
% 43.67/6.05  --abstr_cl_out                          false
% 43.67/6.05  
% 43.67/6.05  ------ Global Options
% 43.67/6.05  
% 43.67/6.05  --schedule                              default
% 43.67/6.05  --add_important_lit                     false
% 43.67/6.05  --prop_solver_per_cl                    1000
% 43.67/6.05  --min_unsat_core                        false
% 43.67/6.05  --soft_assumptions                      false
% 43.67/6.05  --soft_lemma_size                       3
% 43.67/6.05  --prop_impl_unit_size                   0
% 43.67/6.05  --prop_impl_unit                        []
% 43.67/6.05  --share_sel_clauses                     true
% 43.67/6.05  --reset_solvers                         false
% 43.67/6.05  --bc_imp_inh                            [conj_cone]
% 43.67/6.05  --conj_cone_tolerance                   3.
% 43.67/6.05  --extra_neg_conj                        none
% 43.67/6.05  --large_theory_mode                     true
% 43.67/6.05  --prolific_symb_bound                   200
% 43.67/6.05  --lt_threshold                          2000
% 43.67/6.05  --clause_weak_htbl                      true
% 43.67/6.05  --gc_record_bc_elim                     false
% 43.67/6.05  
% 43.67/6.05  ------ Preprocessing Options
% 43.67/6.05  
% 43.67/6.05  --preprocessing_flag                    true
% 43.67/6.05  --time_out_prep_mult                    0.1
% 43.67/6.05  --splitting_mode                        input
% 43.67/6.05  --splitting_grd                         true
% 43.67/6.05  --splitting_cvd                         false
% 43.67/6.05  --splitting_cvd_svl                     false
% 43.67/6.05  --splitting_nvd                         32
% 43.67/6.05  --sub_typing                            true
% 43.67/6.05  --prep_gs_sim                           true
% 43.67/6.05  --prep_unflatten                        true
% 43.67/6.05  --prep_res_sim                          true
% 43.67/6.05  --prep_upred                            true
% 43.67/6.05  --prep_sem_filter                       exhaustive
% 43.67/6.05  --prep_sem_filter_out                   false
% 43.67/6.05  --pred_elim                             true
% 43.67/6.05  --res_sim_input                         true
% 43.67/6.05  --eq_ax_congr_red                       true
% 43.67/6.05  --pure_diseq_elim                       true
% 43.67/6.05  --brand_transform                       false
% 43.67/6.05  --non_eq_to_eq                          false
% 43.67/6.05  --prep_def_merge                        true
% 43.67/6.05  --prep_def_merge_prop_impl              false
% 43.67/6.05  --prep_def_merge_mbd                    true
% 43.67/6.05  --prep_def_merge_tr_red                 false
% 43.67/6.05  --prep_def_merge_tr_cl                  false
% 43.67/6.05  --smt_preprocessing                     true
% 43.67/6.05  --smt_ac_axioms                         fast
% 43.67/6.05  --preprocessed_out                      false
% 43.67/6.05  --preprocessed_stats                    false
% 43.67/6.05  
% 43.67/6.05  ------ Abstraction refinement Options
% 43.67/6.05  
% 43.67/6.05  --abstr_ref                             []
% 43.67/6.05  --abstr_ref_prep                        false
% 43.67/6.05  --abstr_ref_until_sat                   false
% 43.67/6.05  --abstr_ref_sig_restrict                funpre
% 43.67/6.05  --abstr_ref_af_restrict_to_split_sk     false
% 43.67/6.05  --abstr_ref_under                       []
% 43.67/6.05  
% 43.67/6.05  ------ SAT Options
% 43.67/6.05  
% 43.67/6.05  --sat_mode                              false
% 43.67/6.05  --sat_fm_restart_options                ""
% 43.67/6.05  --sat_gr_def                            false
% 43.67/6.05  --sat_epr_types                         true
% 43.67/6.05  --sat_non_cyclic_types                  false
% 43.67/6.05  --sat_finite_models                     false
% 43.67/6.05  --sat_fm_lemmas                         false
% 43.67/6.05  --sat_fm_prep                           false
% 43.67/6.05  --sat_fm_uc_incr                        true
% 43.67/6.05  --sat_out_model                         small
% 43.67/6.05  --sat_out_clauses                       false
% 43.67/6.05  
% 43.67/6.05  ------ QBF Options
% 43.67/6.05  
% 43.67/6.05  --qbf_mode                              false
% 43.67/6.05  --qbf_elim_univ                         false
% 43.67/6.05  --qbf_dom_inst                          none
% 43.67/6.05  --qbf_dom_pre_inst                      false
% 43.67/6.05  --qbf_sk_in                             false
% 43.67/6.05  --qbf_pred_elim                         true
% 43.67/6.05  --qbf_split                             512
% 43.67/6.05  
% 43.67/6.05  ------ BMC1 Options
% 43.67/6.05  
% 43.67/6.05  --bmc1_incremental                      false
% 43.67/6.05  --bmc1_axioms                           reachable_all
% 43.67/6.05  --bmc1_min_bound                        0
% 43.67/6.05  --bmc1_max_bound                        -1
% 43.67/6.05  --bmc1_max_bound_default                -1
% 43.67/6.05  --bmc1_symbol_reachability              true
% 43.67/6.05  --bmc1_property_lemmas                  false
% 43.67/6.05  --bmc1_k_induction                      false
% 43.67/6.05  --bmc1_non_equiv_states                 false
% 43.67/6.05  --bmc1_deadlock                         false
% 43.67/6.05  --bmc1_ucm                              false
% 43.67/6.05  --bmc1_add_unsat_core                   none
% 43.67/6.05  --bmc1_unsat_core_children              false
% 43.67/6.05  --bmc1_unsat_core_extrapolate_axioms    false
% 43.67/6.05  --bmc1_out_stat                         full
% 43.67/6.05  --bmc1_ground_init                      false
% 43.67/6.05  --bmc1_pre_inst_next_state              false
% 43.67/6.05  --bmc1_pre_inst_state                   false
% 43.67/6.05  --bmc1_pre_inst_reach_state             false
% 43.67/6.05  --bmc1_out_unsat_core                   false
% 43.67/6.05  --bmc1_aig_witness_out                  false
% 43.67/6.05  --bmc1_verbose                          false
% 43.67/6.05  --bmc1_dump_clauses_tptp                false
% 43.67/6.05  --bmc1_dump_unsat_core_tptp             false
% 43.67/6.05  --bmc1_dump_file                        -
% 43.67/6.05  --bmc1_ucm_expand_uc_limit              128
% 43.67/6.05  --bmc1_ucm_n_expand_iterations          6
% 43.67/6.05  --bmc1_ucm_extend_mode                  1
% 43.67/6.05  --bmc1_ucm_init_mode                    2
% 43.67/6.05  --bmc1_ucm_cone_mode                    none
% 43.67/6.05  --bmc1_ucm_reduced_relation_type        0
% 43.67/6.05  --bmc1_ucm_relax_model                  4
% 43.67/6.05  --bmc1_ucm_full_tr_after_sat            true
% 43.67/6.05  --bmc1_ucm_expand_neg_assumptions       false
% 43.67/6.05  --bmc1_ucm_layered_model                none
% 43.67/6.05  --bmc1_ucm_max_lemma_size               10
% 43.67/6.05  
% 43.67/6.05  ------ AIG Options
% 43.67/6.05  
% 43.67/6.05  --aig_mode                              false
% 43.67/6.05  
% 43.67/6.05  ------ Instantiation Options
% 43.67/6.05  
% 43.67/6.05  --instantiation_flag                    true
% 43.67/6.05  --inst_sos_flag                         true
% 43.67/6.05  --inst_sos_phase                        true
% 43.67/6.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.67/6.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.67/6.05  --inst_lit_sel_side                     none
% 43.67/6.05  --inst_solver_per_active                1400
% 43.67/6.05  --inst_solver_calls_frac                1.
% 43.67/6.05  --inst_passive_queue_type               priority_queues
% 43.67/6.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.67/6.05  --inst_passive_queues_freq              [25;2]
% 43.67/6.05  --inst_dismatching                      true
% 43.67/6.05  --inst_eager_unprocessed_to_passive     true
% 43.67/6.05  --inst_prop_sim_given                   true
% 43.67/6.05  --inst_prop_sim_new                     false
% 43.67/6.05  --inst_subs_new                         false
% 43.67/6.05  --inst_eq_res_simp                      false
% 43.67/6.05  --inst_subs_given                       false
% 43.67/6.05  --inst_orphan_elimination               true
% 43.67/6.05  --inst_learning_loop_flag               true
% 43.67/6.05  --inst_learning_start                   3000
% 43.67/6.05  --inst_learning_factor                  2
% 43.67/6.05  --inst_start_prop_sim_after_learn       3
% 43.67/6.05  --inst_sel_renew                        solver
% 43.67/6.05  --inst_lit_activity_flag                true
% 43.67/6.05  --inst_restr_to_given                   false
% 43.67/6.05  --inst_activity_threshold               500
% 43.67/6.05  --inst_out_proof                        true
% 43.67/6.05  
% 43.67/6.05  ------ Resolution Options
% 43.67/6.05  
% 43.67/6.05  --resolution_flag                       false
% 43.67/6.05  --res_lit_sel                           adaptive
% 43.67/6.05  --res_lit_sel_side                      none
% 43.67/6.05  --res_ordering                          kbo
% 43.67/6.05  --res_to_prop_solver                    active
% 43.67/6.05  --res_prop_simpl_new                    false
% 43.67/6.05  --res_prop_simpl_given                  true
% 43.67/6.05  --res_passive_queue_type                priority_queues
% 43.67/6.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.67/6.05  --res_passive_queues_freq               [15;5]
% 43.67/6.05  --res_forward_subs                      full
% 43.67/6.05  --res_backward_subs                     full
% 43.67/6.05  --res_forward_subs_resolution           true
% 43.67/6.05  --res_backward_subs_resolution          true
% 43.67/6.05  --res_orphan_elimination                true
% 43.67/6.05  --res_time_limit                        2.
% 43.67/6.05  --res_out_proof                         true
% 43.67/6.05  
% 43.67/6.05  ------ Superposition Options
% 43.67/6.05  
% 43.67/6.05  --superposition_flag                    true
% 43.67/6.05  --sup_passive_queue_type                priority_queues
% 43.67/6.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.67/6.05  --sup_passive_queues_freq               [8;1;4]
% 43.67/6.05  --demod_completeness_check              fast
% 43.67/6.05  --demod_use_ground                      true
% 43.67/6.05  --sup_to_prop_solver                    passive
% 43.67/6.05  --sup_prop_simpl_new                    true
% 43.67/6.05  --sup_prop_simpl_given                  true
% 43.67/6.05  --sup_fun_splitting                     true
% 43.67/6.05  --sup_smt_interval                      50000
% 43.67/6.05  
% 43.67/6.05  ------ Superposition Simplification Setup
% 43.67/6.05  
% 43.67/6.05  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 43.67/6.05  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 43.67/6.05  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 43.67/6.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 43.67/6.05  --sup_full_triv                         [TrivRules;PropSubs]
% 43.67/6.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 43.67/6.05  --sup_full_bw                           [BwDemod;BwSubsumption]
% 43.67/6.05  --sup_immed_triv                        [TrivRules]
% 43.67/6.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.67/6.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.67/6.05  --sup_immed_bw_main                     []
% 43.67/6.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 43.67/6.05  --sup_input_triv                        [Unflattening;TrivRules]
% 43.67/6.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.67/6.05  --sup_input_bw                          []
% 43.67/6.05  
% 43.67/6.05  ------ Combination Options
% 43.67/6.05  
% 43.67/6.05  --comb_res_mult                         3
% 43.67/6.05  --comb_sup_mult                         2
% 43.67/6.05  --comb_inst_mult                        10
% 43.67/6.05  
% 43.67/6.05  ------ Debug Options
% 43.67/6.05  
% 43.67/6.05  --dbg_backtrace                         false
% 43.67/6.05  --dbg_dump_prop_clauses                 false
% 43.67/6.05  --dbg_dump_prop_clauses_file            -
% 43.67/6.05  --dbg_out_stat                          false
% 43.67/6.05  
% 43.67/6.05  
% 43.67/6.05  
% 43.67/6.05  
% 43.67/6.05  ------ Proving...
% 43.67/6.05  
% 43.67/6.05  
% 43.67/6.05  % SZS status Theorem for theBenchmark.p
% 43.67/6.05  
% 43.67/6.05   Resolution empty clause
% 43.67/6.05  
% 43.67/6.05  % SZS output start CNFRefutation for theBenchmark.p
% 43.67/6.05  
% 43.67/6.05  fof(f11,axiom,(
% 43.67/6.05    ! [X0,X1,X2] : (k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) & k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2))),
% 43.67/6.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.67/6.05  
% 43.67/6.05  fof(f38,plain,(
% 43.67/6.05    ( ! [X2,X0,X1] : (k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2)) )),
% 43.67/6.05    inference(cnf_transformation,[],[f11])).
% 43.67/6.05  
% 43.67/6.05  fof(f10,axiom,(
% 43.67/6.05    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 43.67/6.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.67/6.05  
% 43.67/6.05  fof(f37,plain,(
% 43.67/6.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 43.67/6.05    inference(cnf_transformation,[],[f10])).
% 43.67/6.05  
% 43.67/6.05  fof(f9,axiom,(
% 43.67/6.05    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 43.67/6.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.67/6.05  
% 43.67/6.05  fof(f36,plain,(
% 43.67/6.05    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 43.67/6.05    inference(cnf_transformation,[],[f9])).
% 43.67/6.05  
% 43.67/6.05  fof(f43,plain,(
% 43.67/6.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 43.67/6.05    inference(definition_unfolding,[],[f37,f36])).
% 43.67/6.05  
% 43.67/6.05  fof(f48,plain,(
% 43.67/6.05    ( ! [X2,X0,X1] : (k3_tarski(k1_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) = k2_zfmisc_1(k3_tarski(k1_enumset1(X0,X0,X1)),X2)) )),
% 43.67/6.05    inference(definition_unfolding,[],[f38,f43,f43])).
% 43.67/6.05  
% 43.67/6.05  fof(f8,axiom,(
% 43.67/6.05    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 43.67/6.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.67/6.05  
% 43.67/6.05  fof(f35,plain,(
% 43.67/6.05    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 43.67/6.05    inference(cnf_transformation,[],[f8])).
% 43.67/6.05  
% 43.67/6.05  fof(f46,plain,(
% 43.67/6.05    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 43.67/6.05    inference(definition_unfolding,[],[f35,f36,f36])).
% 43.67/6.05  
% 43.67/6.05  fof(f7,axiom,(
% 43.67/6.05    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 43.67/6.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.67/6.05  
% 43.67/6.05  fof(f34,plain,(
% 43.67/6.05    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 43.67/6.05    inference(cnf_transformation,[],[f7])).
% 43.67/6.05  
% 43.67/6.05  fof(f45,plain,(
% 43.67/6.05    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 43.67/6.05    inference(definition_unfolding,[],[f34,f43])).
% 43.67/6.05  
% 43.67/6.05  fof(f12,conjecture,(
% 43.67/6.05    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 43.67/6.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.67/6.05  
% 43.67/6.05  fof(f13,negated_conjecture,(
% 43.67/6.05    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 43.67/6.05    inference(negated_conjecture,[],[f12])).
% 43.67/6.05  
% 43.67/6.05  fof(f20,plain,(
% 43.67/6.05    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 43.67/6.05    inference(ennf_transformation,[],[f13])).
% 43.67/6.05  
% 43.67/6.05  fof(f21,plain,(
% 43.67/6.05    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 43.67/6.05    inference(flattening,[],[f20])).
% 43.67/6.05  
% 43.67/6.05  fof(f24,plain,(
% 43.67/6.05    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 43.67/6.05    introduced(choice_axiom,[])).
% 43.67/6.05  
% 43.67/6.05  fof(f25,plain,(
% 43.67/6.05    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 43.67/6.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f21,f24])).
% 43.67/6.05  
% 43.67/6.05  fof(f41,plain,(
% 43.67/6.05    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 43.67/6.05    inference(cnf_transformation,[],[f25])).
% 43.67/6.05  
% 43.67/6.05  fof(f5,axiom,(
% 43.67/6.05    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 43.67/6.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.67/6.05  
% 43.67/6.05  fof(f17,plain,(
% 43.67/6.05    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 43.67/6.05    inference(ennf_transformation,[],[f5])).
% 43.67/6.05  
% 43.67/6.05  fof(f18,plain,(
% 43.67/6.05    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 43.67/6.05    inference(flattening,[],[f17])).
% 43.67/6.05  
% 43.67/6.05  fof(f32,plain,(
% 43.67/6.05    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 43.67/6.05    inference(cnf_transformation,[],[f18])).
% 43.67/6.05  
% 43.67/6.05  fof(f40,plain,(
% 43.67/6.05    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 43.67/6.05    inference(cnf_transformation,[],[f25])).
% 43.67/6.05  
% 43.67/6.05  fof(f39,plain,(
% 43.67/6.05    ( ! [X2,X0,X1] : (k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1))) )),
% 43.67/6.05    inference(cnf_transformation,[],[f11])).
% 43.67/6.05  
% 43.67/6.05  fof(f47,plain,(
% 43.67/6.05    ( ! [X2,X0,X1] : (k3_tarski(k1_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(X2,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 43.67/6.05    inference(definition_unfolding,[],[f39,f43,f43])).
% 43.67/6.05  
% 43.67/6.05  fof(f4,axiom,(
% 43.67/6.05    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 43.67/6.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.67/6.05  
% 43.67/6.05  fof(f15,plain,(
% 43.67/6.05    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 43.67/6.05    inference(ennf_transformation,[],[f4])).
% 43.67/6.05  
% 43.67/6.05  fof(f16,plain,(
% 43.67/6.05    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 43.67/6.05    inference(flattening,[],[f15])).
% 43.67/6.05  
% 43.67/6.05  fof(f31,plain,(
% 43.67/6.05    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 43.67/6.05    inference(cnf_transformation,[],[f16])).
% 43.67/6.05  
% 43.67/6.05  fof(f44,plain,(
% 43.67/6.05    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),k3_tarski(k1_enumset1(X1,X1,X3))) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 43.67/6.05    inference(definition_unfolding,[],[f31,f43,f43])).
% 43.67/6.05  
% 43.67/6.05  fof(f42,plain,(
% 43.67/6.05    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 43.67/6.05    inference(cnf_transformation,[],[f25])).
% 43.67/6.05  
% 43.67/6.05  fof(f49,plain,(
% 43.67/6.05    ~r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5))))),
% 43.67/6.05    inference(definition_unfolding,[],[f42,f43,f43,f43])).
% 43.67/6.05  
% 43.67/6.05  cnf(c_11,plain,
% 43.67/6.05      ( k3_tarski(k1_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(k3_tarski(k1_enumset1(X0,X0,X2)),X1) ),
% 43.67/6.05      inference(cnf_transformation,[],[f48]) ).
% 43.67/6.05  
% 43.67/6.05  cnf(c_9,plain,
% 43.67/6.05      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 43.67/6.05      inference(cnf_transformation,[],[f46]) ).
% 43.67/6.05  
% 43.67/6.05  cnf(c_8,plain,
% 43.67/6.05      ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
% 43.67/6.05      inference(cnf_transformation,[],[f45]) ).
% 43.67/6.05  
% 43.67/6.05  cnf(c_357,plain,
% 43.67/6.05      ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) = iProver_top ),
% 43.67/6.05      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 43.67/6.05  
% 43.67/6.05  cnf(c_743,plain,
% 43.67/6.05      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0))) = iProver_top ),
% 43.67/6.05      inference(superposition,[status(thm)],[c_9,c_357]) ).
% 43.67/6.05  
% 43.67/6.05  cnf(c_857,plain,
% 43.67/6.05      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k3_tarski(k1_enumset1(X2,X2,X0)),X1)) = iProver_top ),
% 43.67/6.05      inference(superposition,[status(thm)],[c_11,c_743]) ).
% 43.67/6.05  
% 43.67/6.05  cnf(c_13,negated_conjecture,
% 43.67/6.05      ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
% 43.67/6.05      inference(cnf_transformation,[],[f41]) ).
% 43.67/6.05  
% 43.67/6.05  cnf(c_355,plain,
% 43.67/6.05      ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 43.67/6.05      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 43.67/6.05  
% 43.67/6.05  cnf(c_6,plain,
% 43.67/6.05      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 43.67/6.05      inference(cnf_transformation,[],[f32]) ).
% 43.67/6.05  
% 43.67/6.05  cnf(c_359,plain,
% 43.67/6.05      ( r1_tarski(X0,X1) != iProver_top
% 43.67/6.05      | r1_tarski(X1,X2) != iProver_top
% 43.67/6.05      | r1_tarski(X0,X2) = iProver_top ),
% 43.67/6.05      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 43.67/6.05  
% 43.67/6.05  cnf(c_1711,plain,
% 43.67/6.05      ( r1_tarski(k2_zfmisc_1(sK4,sK5),X0) != iProver_top
% 43.67/6.05      | r1_tarski(sK1,X0) = iProver_top ),
% 43.67/6.05      inference(superposition,[status(thm)],[c_355,c_359]) ).
% 43.67/6.05  
% 43.67/6.05  cnf(c_2209,plain,
% 43.67/6.05      ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(X0,X0,sK4)),sK5)) = iProver_top ),
% 43.67/6.05      inference(superposition,[status(thm)],[c_857,c_1711]) ).
% 43.67/6.05  
% 43.67/6.05  cnf(c_855,plain,
% 43.67/6.05      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k3_tarski(k1_enumset1(X0,X0,X2)),X1)) = iProver_top ),
% 43.67/6.05      inference(superposition,[status(thm)],[c_11,c_357]) ).
% 43.67/6.05  
% 43.67/6.05  cnf(c_14,negated_conjecture,
% 43.67/6.05      ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
% 43.67/6.05      inference(cnf_transformation,[],[f40]) ).
% 43.67/6.05  
% 43.67/6.05  cnf(c_354,plain,
% 43.67/6.05      ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 43.67/6.05      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 43.67/6.05  
% 43.67/6.05  cnf(c_1712,plain,
% 43.67/6.05      ( r1_tarski(k2_zfmisc_1(sK2,sK3),X0) != iProver_top
% 43.67/6.05      | r1_tarski(sK0,X0) = iProver_top ),
% 43.67/6.05      inference(superposition,[status(thm)],[c_354,c_359]) ).
% 43.67/6.05  
% 43.67/6.05  cnf(c_2234,plain,
% 43.67/6.05      ( r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,X0)),sK3)) = iProver_top ),
% 43.67/6.05      inference(superposition,[status(thm)],[c_855,c_1712]) ).
% 43.67/6.05  
% 43.67/6.05  cnf(c_10,plain,
% 43.67/6.05      ( k3_tarski(k1_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))) = k2_zfmisc_1(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ),
% 43.67/6.05      inference(cnf_transformation,[],[f47]) ).
% 43.67/6.05  
% 43.67/6.05  cnf(c_5,plain,
% 43.67/6.05      ( ~ r1_tarski(X0,X1)
% 43.67/6.05      | ~ r1_tarski(X2,X3)
% 43.67/6.05      | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),k3_tarski(k1_enumset1(X1,X1,X3))) ),
% 43.67/6.05      inference(cnf_transformation,[],[f44]) ).
% 43.67/6.05  
% 43.67/6.05  cnf(c_360,plain,
% 43.67/6.05      ( r1_tarski(X0,X1) != iProver_top
% 43.67/6.05      | r1_tarski(X2,X3) != iProver_top
% 43.67/6.05      | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),k3_tarski(k1_enumset1(X1,X1,X3))) = iProver_top ),
% 43.67/6.05      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 43.67/6.05  
% 43.67/6.05  cnf(c_3024,plain,
% 43.67/6.05      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 43.67/6.05      | r1_tarski(X3,k2_zfmisc_1(X1,X4)) != iProver_top
% 43.67/6.05      | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X3)),k2_zfmisc_1(X1,k3_tarski(k1_enumset1(X2,X2,X4)))) = iProver_top ),
% 43.67/6.05      inference(superposition,[status(thm)],[c_10,c_360]) ).
% 43.67/6.05  
% 43.67/6.05  cnf(c_12,negated_conjecture,
% 43.67/6.05      ( ~ r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) ),
% 43.67/6.05      inference(cnf_transformation,[],[f49]) ).
% 43.67/6.05  
% 43.67/6.05  cnf(c_356,plain,
% 43.67/6.05      ( r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) != iProver_top ),
% 43.67/6.05      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 43.67/6.05  
% 43.67/6.05  cnf(c_163199,plain,
% 43.67/6.05      ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK5)) != iProver_top
% 43.67/6.05      | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK3)) != iProver_top ),
% 43.67/6.05      inference(superposition,[status(thm)],[c_3024,c_356]) ).
% 43.67/6.05  
% 43.67/6.05  cnf(c_165116,plain,
% 43.67/6.05      ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK5)) != iProver_top ),
% 43.67/6.05      inference(superposition,[status(thm)],[c_2234,c_163199]) ).
% 43.67/6.05  
% 43.67/6.05  cnf(c_165730,plain,
% 43.67/6.05      ( $false ),
% 43.67/6.05      inference(superposition,[status(thm)],[c_2209,c_165116]) ).
% 43.67/6.05  
% 43.67/6.05  
% 43.67/6.05  % SZS output end CNFRefutation for theBenchmark.p
% 43.67/6.05  
% 43.67/6.05  ------                               Statistics
% 43.67/6.05  
% 43.67/6.05  ------ General
% 43.67/6.05  
% 43.67/6.05  abstr_ref_over_cycles:                  0
% 43.67/6.05  abstr_ref_under_cycles:                 0
% 43.67/6.05  gc_basic_clause_elim:                   0
% 43.67/6.05  forced_gc_time:                         0
% 43.67/6.05  parsing_time:                           0.007
% 43.67/6.05  unif_index_cands_time:                  0.
% 43.67/6.05  unif_index_add_time:                    0.
% 43.67/6.05  orderings_time:                         0.
% 43.67/6.05  out_proof_time:                         0.007
% 43.67/6.05  total_time:                             5.131
% 43.67/6.05  num_of_symbols:                         42
% 43.67/6.05  num_of_terms:                           132005
% 43.67/6.05  
% 43.67/6.05  ------ Preprocessing
% 43.67/6.05  
% 43.67/6.05  num_of_splits:                          0
% 43.67/6.05  num_of_split_atoms:                     0
% 43.67/6.05  num_of_reused_defs:                     0
% 43.67/6.05  num_eq_ax_congr_red:                    6
% 43.67/6.05  num_of_sem_filtered_clauses:            1
% 43.67/6.05  num_of_subtypes:                        0
% 43.67/6.05  monotx_restored_types:                  0
% 43.67/6.05  sat_num_of_epr_types:                   0
% 43.67/6.05  sat_num_of_non_cyclic_types:            0
% 43.67/6.05  sat_guarded_non_collapsed_types:        0
% 43.67/6.05  num_pure_diseq_elim:                    0
% 43.67/6.05  simp_replaced_by:                       0
% 43.67/6.05  res_preprocessed:                       69
% 43.67/6.05  prep_upred:                             0
% 43.67/6.05  prep_unflattend:                        0
% 43.67/6.05  smt_new_axioms:                         0
% 43.67/6.05  pred_elim_cands:                        1
% 43.67/6.05  pred_elim:                              0
% 43.67/6.05  pred_elim_cl:                           0
% 43.67/6.05  pred_elim_cycles:                       2
% 43.67/6.05  merged_defs:                            0
% 43.67/6.05  merged_defs_ncl:                        0
% 43.67/6.05  bin_hyper_res:                          0
% 43.67/6.05  prep_cycles:                            4
% 43.67/6.05  pred_elim_time:                         0.
% 43.67/6.05  splitting_time:                         0.
% 43.67/6.05  sem_filter_time:                        0.
% 43.67/6.05  monotx_time:                            0.
% 43.67/6.05  subtype_inf_time:                       0.
% 43.67/6.05  
% 43.67/6.05  ------ Problem properties
% 43.67/6.05  
% 43.67/6.05  clauses:                                14
% 43.67/6.05  conjectures:                            3
% 43.67/6.05  epr:                                    3
% 43.67/6.05  horn:                                   14
% 43.67/6.05  ground:                                 3
% 43.67/6.05  unary:                                  9
% 43.67/6.05  binary:                                 2
% 43.67/6.05  lits:                                   22
% 43.67/6.05  lits_eq:                                6
% 43.67/6.05  fd_pure:                                0
% 43.67/6.05  fd_pseudo:                              0
% 43.67/6.05  fd_cond:                                0
% 43.67/6.05  fd_pseudo_cond:                         1
% 43.67/6.05  ac_symbols:                             0
% 43.67/6.05  
% 43.67/6.05  ------ Propositional Solver
% 43.67/6.05  
% 43.67/6.05  prop_solver_calls:                      45
% 43.67/6.05  prop_fast_solver_calls:                 960
% 43.67/6.05  smt_solver_calls:                       0
% 43.67/6.05  smt_fast_solver_calls:                  0
% 43.67/6.05  prop_num_of_clauses:                    44755
% 43.67/6.05  prop_preprocess_simplified:             66970
% 43.67/6.05  prop_fo_subsumed:                       0
% 43.67/6.05  prop_solver_time:                       0.
% 43.67/6.05  smt_solver_time:                        0.
% 43.67/6.05  smt_fast_solver_time:                   0.
% 43.67/6.05  prop_fast_solver_time:                  0.
% 43.67/6.05  prop_unsat_core_time:                   0.
% 43.67/6.05  
% 43.67/6.05  ------ QBF
% 43.67/6.05  
% 43.67/6.05  qbf_q_res:                              0
% 43.67/6.05  qbf_num_tautologies:                    0
% 43.67/6.05  qbf_prep_cycles:                        0
% 43.67/6.05  
% 43.67/6.05  ------ BMC1
% 43.67/6.05  
% 43.67/6.05  bmc1_current_bound:                     -1
% 43.67/6.05  bmc1_last_solved_bound:                 -1
% 43.67/6.05  bmc1_unsat_core_size:                   -1
% 43.67/6.05  bmc1_unsat_core_parents_size:           -1
% 43.67/6.05  bmc1_merge_next_fun:                    0
% 43.67/6.05  bmc1_unsat_core_clauses_time:           0.
% 43.67/6.05  
% 43.67/6.05  ------ Instantiation
% 43.67/6.05  
% 43.67/6.05  inst_num_of_clauses:                    9827
% 43.67/6.05  inst_num_in_passive:                    3360
% 43.67/6.05  inst_num_in_active:                     2439
% 43.67/6.05  inst_num_in_unprocessed:                4029
% 43.67/6.05  inst_num_of_loops:                      2990
% 43.67/6.05  inst_num_of_learning_restarts:          0
% 43.67/6.05  inst_num_moves_active_passive:          546
% 43.67/6.05  inst_lit_activity:                      0
% 43.67/6.05  inst_lit_activity_moves:                2
% 43.67/6.05  inst_num_tautologies:                   0
% 43.67/6.05  inst_num_prop_implied:                  0
% 43.67/6.05  inst_num_existing_simplified:           0
% 43.67/6.05  inst_num_eq_res_simplified:             0
% 43.67/6.05  inst_num_child_elim:                    0
% 43.67/6.05  inst_num_of_dismatching_blockings:      30946
% 43.67/6.05  inst_num_of_non_proper_insts:           21341
% 43.67/6.05  inst_num_of_duplicates:                 0
% 43.67/6.05  inst_inst_num_from_inst_to_res:         0
% 43.67/6.05  inst_dismatching_checking_time:         0.
% 43.67/6.05  
% 43.67/6.05  ------ Resolution
% 43.67/6.05  
% 43.67/6.05  res_num_of_clauses:                     0
% 43.67/6.05  res_num_in_passive:                     0
% 43.67/6.05  res_num_in_active:                      0
% 43.67/6.05  res_num_of_loops:                       73
% 43.67/6.05  res_forward_subset_subsumed:            3855
% 43.67/6.05  res_backward_subset_subsumed:           6
% 43.67/6.05  res_forward_subsumed:                   0
% 43.67/6.05  res_backward_subsumed:                  0
% 43.67/6.05  res_forward_subsumption_resolution:     0
% 43.67/6.05  res_backward_subsumption_resolution:    0
% 43.67/6.05  res_clause_to_clause_subsumption:       63991
% 43.67/6.05  res_orphan_elimination:                 0
% 43.67/6.05  res_tautology_del:                      2449
% 43.67/6.05  res_num_eq_res_simplified:              0
% 43.67/6.05  res_num_sel_changes:                    0
% 43.67/6.05  res_moves_from_active_to_pass:          0
% 43.67/6.05  
% 43.67/6.05  ------ Superposition
% 43.67/6.05  
% 43.67/6.05  sup_time_total:                         0.
% 43.67/6.05  sup_time_generating:                    0.
% 43.67/6.05  sup_time_sim_full:                      0.
% 43.67/6.05  sup_time_sim_immed:                     0.
% 43.67/6.05  
% 43.67/6.05  sup_num_of_clauses:                     5200
% 43.67/6.05  sup_num_in_active:                      594
% 43.67/6.05  sup_num_in_passive:                     4606
% 43.67/6.05  sup_num_of_loops:                       596
% 43.67/6.05  sup_fw_superposition:                   17298
% 43.67/6.05  sup_bw_superposition:                   9813
% 43.67/6.05  sup_immediate_simplified:               9447
% 43.67/6.05  sup_given_eliminated:                   0
% 43.67/6.05  comparisons_done:                       0
% 43.67/6.05  comparisons_avoided:                    0
% 43.67/6.05  
% 43.67/6.05  ------ Simplifications
% 43.67/6.05  
% 43.67/6.05  
% 43.67/6.05  sim_fw_subset_subsumed:                 2
% 43.67/6.05  sim_bw_subset_subsumed:                 2
% 43.67/6.05  sim_fw_subsumed:                        2354
% 43.67/6.05  sim_bw_subsumed:                        58
% 43.67/6.05  sim_fw_subsumption_res:                 0
% 43.67/6.05  sim_bw_subsumption_res:                 0
% 43.67/6.05  sim_tautology_del:                      229
% 43.67/6.05  sim_eq_tautology_del:                   2074
% 43.67/6.05  sim_eq_res_simp:                        0
% 43.67/6.05  sim_fw_demodulated:                     4865
% 43.67/6.05  sim_bw_demodulated:                     0
% 43.67/6.05  sim_light_normalised:                   3378
% 43.67/6.05  sim_joinable_taut:                      0
% 43.67/6.05  sim_joinable_simp:                      0
% 43.67/6.05  sim_ac_normalised:                      0
% 43.67/6.05  sim_smt_subsumption:                    0
% 43.67/6.05  
%------------------------------------------------------------------------------
