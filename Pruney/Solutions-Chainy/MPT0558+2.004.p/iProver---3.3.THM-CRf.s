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
% DateTime   : Thu Dec  3 11:46:49 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 151 expanded)
%              Number of clauses        :   37 (  55 expanded)
%              Number of leaves         :   10 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  157 ( 397 expanded)
%              Number of equality atoms :   76 ( 163 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0))
          & v1_relat_1(X1) )
     => ( k2_relat_1(k5_relat_1(X0,sK1)) != k9_relat_1(sK1,k2_relat_1(X0))
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f20,f19])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f30,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f17])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f33,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f23])).

fof(f32,plain,(
    k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_9,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_347,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_10,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_346,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_349,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_348,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_821,plain,
    ( k7_relat_1(k5_relat_1(X0,X1),k1_relat_1(X0)) = k5_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_349,c_348])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_352,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2782,plain,
    ( k7_relat_1(k5_relat_1(X0,X1),k1_relat_1(X0)) = k5_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_821,c_352])).

cnf(c_2788,plain,
    ( k7_relat_1(k5_relat_1(sK0,X0),k1_relat_1(sK0)) = k5_relat_1(sK0,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_346,c_2782])).

cnf(c_3032,plain,
    ( k7_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_347,c_2788])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_351,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_694,plain,
    ( k2_relat_1(k7_relat_1(k5_relat_1(X0,X1),X2)) = k9_relat_1(k5_relat_1(X0,X1),X2)
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_352,c_351])).

cnf(c_1619,plain,
    ( k2_relat_1(k7_relat_1(k5_relat_1(sK0,X0),X1)) = k9_relat_1(k5_relat_1(sK0,X0),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_346,c_694])).

cnf(c_1833,plain,
    ( k2_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X0)) = k9_relat_1(k5_relat_1(sK0,sK1),X0) ),
    inference(superposition,[status(thm)],[c_347,c_1619])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(k5_relat_1(X0,X1),X2) = k9_relat_1(X1,k9_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_350,plain,
    ( k9_relat_1(k5_relat_1(X0,X1),X2) = k9_relat_1(X1,k9_relat_1(X0,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_850,plain,
    ( k9_relat_1(X0,k9_relat_1(sK0,X1)) = k9_relat_1(k5_relat_1(sK0,X0),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_346,c_350])).

cnf(c_1052,plain,
    ( k9_relat_1(k5_relat_1(sK0,sK1),X0) = k9_relat_1(sK1,k9_relat_1(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_347,c_850])).

cnf(c_1839,plain,
    ( k2_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X0)) = k9_relat_1(sK1,k9_relat_1(sK0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1833,c_1052])).

cnf(c_3048,plain,
    ( k9_relat_1(sK1,k9_relat_1(sK0,k1_relat_1(sK0))) = k2_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_3032,c_1839])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_353,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_686,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_353,c_348])).

cnf(c_1390,plain,
    ( k7_relat_1(sK0,k1_relat_1(sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_346,c_686])).

cnf(c_523,plain,
    ( k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0) ),
    inference(superposition,[status(thm)],[c_346,c_351])).

cnf(c_1495,plain,
    ( k9_relat_1(sK0,k1_relat_1(sK0)) = k2_relat_1(sK0) ),
    inference(superposition,[status(thm)],[c_1390,c_523])).

cnf(c_3049,plain,
    ( k9_relat_1(sK1,k2_relat_1(sK0)) = k2_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_3048,c_1495])).

cnf(c_8,negated_conjecture,
    ( k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_17799,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK1)) != k2_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_3049,c_8])).

cnf(c_176,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_785,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK1)) = k2_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_176])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17799,c_785])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:28:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.30/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.02  
% 2.30/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.30/1.02  
% 2.30/1.02  ------  iProver source info
% 2.30/1.02  
% 2.30/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.30/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.30/1.02  git: non_committed_changes: false
% 2.30/1.02  git: last_make_outside_of_git: false
% 2.30/1.02  
% 2.30/1.02  ------ 
% 2.30/1.02  
% 2.30/1.02  ------ Input Options
% 2.30/1.02  
% 2.30/1.02  --out_options                           all
% 2.30/1.02  --tptp_safe_out                         true
% 2.30/1.02  --problem_path                          ""
% 2.30/1.02  --include_path                          ""
% 2.30/1.02  --clausifier                            res/vclausify_rel
% 2.30/1.02  --clausifier_options                    --mode clausify
% 2.30/1.02  --stdin                                 false
% 2.30/1.02  --stats_out                             all
% 2.30/1.02  
% 2.30/1.02  ------ General Options
% 2.30/1.02  
% 2.30/1.02  --fof                                   false
% 2.30/1.02  --time_out_real                         305.
% 2.30/1.02  --time_out_virtual                      -1.
% 2.30/1.02  --symbol_type_check                     false
% 2.30/1.02  --clausify_out                          false
% 2.30/1.02  --sig_cnt_out                           false
% 2.30/1.02  --trig_cnt_out                          false
% 2.30/1.02  --trig_cnt_out_tolerance                1.
% 2.30/1.02  --trig_cnt_out_sk_spl                   false
% 2.30/1.02  --abstr_cl_out                          false
% 2.30/1.02  
% 2.30/1.02  ------ Global Options
% 2.30/1.02  
% 2.30/1.02  --schedule                              default
% 2.30/1.02  --add_important_lit                     false
% 2.30/1.02  --prop_solver_per_cl                    1000
% 2.30/1.02  --min_unsat_core                        false
% 2.30/1.02  --soft_assumptions                      false
% 2.30/1.02  --soft_lemma_size                       3
% 2.30/1.02  --prop_impl_unit_size                   0
% 2.30/1.02  --prop_impl_unit                        []
% 2.30/1.02  --share_sel_clauses                     true
% 2.30/1.02  --reset_solvers                         false
% 2.30/1.02  --bc_imp_inh                            [conj_cone]
% 2.30/1.02  --conj_cone_tolerance                   3.
% 2.30/1.02  --extra_neg_conj                        none
% 2.30/1.02  --large_theory_mode                     true
% 2.30/1.02  --prolific_symb_bound                   200
% 2.30/1.02  --lt_threshold                          2000
% 2.30/1.02  --clause_weak_htbl                      true
% 2.30/1.02  --gc_record_bc_elim                     false
% 2.30/1.02  
% 2.30/1.02  ------ Preprocessing Options
% 2.30/1.02  
% 2.30/1.02  --preprocessing_flag                    true
% 2.30/1.02  --time_out_prep_mult                    0.1
% 2.30/1.02  --splitting_mode                        input
% 2.30/1.02  --splitting_grd                         true
% 2.30/1.02  --splitting_cvd                         false
% 2.30/1.02  --splitting_cvd_svl                     false
% 2.30/1.02  --splitting_nvd                         32
% 2.30/1.02  --sub_typing                            true
% 2.30/1.02  --prep_gs_sim                           true
% 2.30/1.02  --prep_unflatten                        true
% 2.30/1.02  --prep_res_sim                          true
% 2.30/1.02  --prep_upred                            true
% 2.30/1.02  --prep_sem_filter                       exhaustive
% 2.30/1.02  --prep_sem_filter_out                   false
% 2.30/1.02  --pred_elim                             true
% 2.30/1.02  --res_sim_input                         true
% 2.30/1.02  --eq_ax_congr_red                       true
% 2.30/1.02  --pure_diseq_elim                       true
% 2.30/1.02  --brand_transform                       false
% 2.30/1.02  --non_eq_to_eq                          false
% 2.30/1.02  --prep_def_merge                        true
% 2.30/1.02  --prep_def_merge_prop_impl              false
% 2.30/1.02  --prep_def_merge_mbd                    true
% 2.30/1.02  --prep_def_merge_tr_red                 false
% 2.30/1.02  --prep_def_merge_tr_cl                  false
% 2.30/1.02  --smt_preprocessing                     true
% 2.30/1.02  --smt_ac_axioms                         fast
% 2.30/1.02  --preprocessed_out                      false
% 2.30/1.02  --preprocessed_stats                    false
% 2.30/1.02  
% 2.30/1.02  ------ Abstraction refinement Options
% 2.30/1.02  
% 2.30/1.02  --abstr_ref                             []
% 2.30/1.02  --abstr_ref_prep                        false
% 2.30/1.02  --abstr_ref_until_sat                   false
% 2.30/1.02  --abstr_ref_sig_restrict                funpre
% 2.30/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.30/1.02  --abstr_ref_under                       []
% 2.30/1.02  
% 2.30/1.02  ------ SAT Options
% 2.30/1.02  
% 2.30/1.02  --sat_mode                              false
% 2.30/1.02  --sat_fm_restart_options                ""
% 2.30/1.02  --sat_gr_def                            false
% 2.30/1.02  --sat_epr_types                         true
% 2.30/1.02  --sat_non_cyclic_types                  false
% 2.30/1.02  --sat_finite_models                     false
% 2.30/1.02  --sat_fm_lemmas                         false
% 2.30/1.02  --sat_fm_prep                           false
% 2.30/1.02  --sat_fm_uc_incr                        true
% 2.30/1.02  --sat_out_model                         small
% 2.30/1.02  --sat_out_clauses                       false
% 2.30/1.02  
% 2.30/1.02  ------ QBF Options
% 2.30/1.02  
% 2.30/1.02  --qbf_mode                              false
% 2.30/1.02  --qbf_elim_univ                         false
% 2.30/1.02  --qbf_dom_inst                          none
% 2.30/1.02  --qbf_dom_pre_inst                      false
% 2.30/1.02  --qbf_sk_in                             false
% 2.30/1.02  --qbf_pred_elim                         true
% 2.30/1.02  --qbf_split                             512
% 2.30/1.02  
% 2.30/1.02  ------ BMC1 Options
% 2.30/1.02  
% 2.30/1.02  --bmc1_incremental                      false
% 2.30/1.02  --bmc1_axioms                           reachable_all
% 2.30/1.02  --bmc1_min_bound                        0
% 2.30/1.02  --bmc1_max_bound                        -1
% 2.30/1.02  --bmc1_max_bound_default                -1
% 2.30/1.02  --bmc1_symbol_reachability              true
% 2.30/1.02  --bmc1_property_lemmas                  false
% 2.30/1.02  --bmc1_k_induction                      false
% 2.30/1.02  --bmc1_non_equiv_states                 false
% 2.30/1.02  --bmc1_deadlock                         false
% 2.30/1.02  --bmc1_ucm                              false
% 2.30/1.02  --bmc1_add_unsat_core                   none
% 2.30/1.02  --bmc1_unsat_core_children              false
% 2.30/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.30/1.02  --bmc1_out_stat                         full
% 2.30/1.02  --bmc1_ground_init                      false
% 2.30/1.02  --bmc1_pre_inst_next_state              false
% 2.30/1.02  --bmc1_pre_inst_state                   false
% 2.30/1.02  --bmc1_pre_inst_reach_state             false
% 2.30/1.02  --bmc1_out_unsat_core                   false
% 2.30/1.02  --bmc1_aig_witness_out                  false
% 2.30/1.02  --bmc1_verbose                          false
% 2.30/1.02  --bmc1_dump_clauses_tptp                false
% 2.30/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.30/1.02  --bmc1_dump_file                        -
% 2.30/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.30/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.30/1.02  --bmc1_ucm_extend_mode                  1
% 2.30/1.02  --bmc1_ucm_init_mode                    2
% 2.30/1.02  --bmc1_ucm_cone_mode                    none
% 2.30/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.30/1.02  --bmc1_ucm_relax_model                  4
% 2.30/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.30/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.30/1.02  --bmc1_ucm_layered_model                none
% 2.30/1.02  --bmc1_ucm_max_lemma_size               10
% 2.30/1.02  
% 2.30/1.02  ------ AIG Options
% 2.30/1.02  
% 2.30/1.02  --aig_mode                              false
% 2.30/1.02  
% 2.30/1.02  ------ Instantiation Options
% 2.30/1.02  
% 2.30/1.02  --instantiation_flag                    true
% 2.30/1.02  --inst_sos_flag                         false
% 2.30/1.02  --inst_sos_phase                        true
% 2.30/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.30/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.30/1.02  --inst_lit_sel_side                     num_symb
% 2.30/1.02  --inst_solver_per_active                1400
% 2.30/1.02  --inst_solver_calls_frac                1.
% 2.30/1.02  --inst_passive_queue_type               priority_queues
% 2.30/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.30/1.02  --inst_passive_queues_freq              [25;2]
% 2.30/1.02  --inst_dismatching                      true
% 2.30/1.02  --inst_eager_unprocessed_to_passive     true
% 2.30/1.02  --inst_prop_sim_given                   true
% 2.30/1.02  --inst_prop_sim_new                     false
% 2.30/1.02  --inst_subs_new                         false
% 2.30/1.02  --inst_eq_res_simp                      false
% 2.30/1.02  --inst_subs_given                       false
% 2.30/1.02  --inst_orphan_elimination               true
% 2.30/1.02  --inst_learning_loop_flag               true
% 2.30/1.02  --inst_learning_start                   3000
% 2.30/1.02  --inst_learning_factor                  2
% 2.30/1.02  --inst_start_prop_sim_after_learn       3
% 2.30/1.02  --inst_sel_renew                        solver
% 2.30/1.02  --inst_lit_activity_flag                true
% 2.30/1.02  --inst_restr_to_given                   false
% 2.30/1.02  --inst_activity_threshold               500
% 2.30/1.02  --inst_out_proof                        true
% 2.30/1.02  
% 2.30/1.02  ------ Resolution Options
% 2.30/1.02  
% 2.30/1.02  --resolution_flag                       true
% 2.30/1.02  --res_lit_sel                           adaptive
% 2.30/1.02  --res_lit_sel_side                      none
% 2.30/1.02  --res_ordering                          kbo
% 2.30/1.02  --res_to_prop_solver                    active
% 2.30/1.02  --res_prop_simpl_new                    false
% 2.30/1.02  --res_prop_simpl_given                  true
% 2.30/1.02  --res_passive_queue_type                priority_queues
% 2.30/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.30/1.03  --res_passive_queues_freq               [15;5]
% 2.30/1.03  --res_forward_subs                      full
% 2.30/1.03  --res_backward_subs                     full
% 2.30/1.03  --res_forward_subs_resolution           true
% 2.30/1.03  --res_backward_subs_resolution          true
% 2.30/1.03  --res_orphan_elimination                true
% 2.30/1.03  --res_time_limit                        2.
% 2.30/1.03  --res_out_proof                         true
% 2.30/1.03  
% 2.30/1.03  ------ Superposition Options
% 2.30/1.03  
% 2.30/1.03  --superposition_flag                    true
% 2.30/1.03  --sup_passive_queue_type                priority_queues
% 2.30/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.30/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.30/1.03  --demod_completeness_check              fast
% 2.30/1.03  --demod_use_ground                      true
% 2.30/1.03  --sup_to_prop_solver                    passive
% 2.30/1.03  --sup_prop_simpl_new                    true
% 2.30/1.03  --sup_prop_simpl_given                  true
% 2.30/1.03  --sup_fun_splitting                     false
% 2.30/1.03  --sup_smt_interval                      50000
% 2.30/1.03  
% 2.30/1.03  ------ Superposition Simplification Setup
% 2.30/1.03  
% 2.30/1.03  --sup_indices_passive                   []
% 2.30/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.30/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.30/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.30/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.30/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.30/1.03  --sup_full_bw                           [BwDemod]
% 2.30/1.03  --sup_immed_triv                        [TrivRules]
% 2.30/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.30/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.30/1.03  --sup_immed_bw_main                     []
% 2.30/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.30/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.30/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.30/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.30/1.03  
% 2.30/1.03  ------ Combination Options
% 2.30/1.03  
% 2.30/1.03  --comb_res_mult                         3
% 2.30/1.03  --comb_sup_mult                         2
% 2.30/1.03  --comb_inst_mult                        10
% 2.30/1.03  
% 2.30/1.03  ------ Debug Options
% 2.30/1.03  
% 2.30/1.03  --dbg_backtrace                         false
% 2.30/1.03  --dbg_dump_prop_clauses                 false
% 2.30/1.03  --dbg_dump_prop_clauses_file            -
% 2.30/1.03  --dbg_out_stat                          false
% 2.30/1.03  ------ Parsing...
% 2.30/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.30/1.03  
% 2.30/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.30/1.03  
% 2.30/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.30/1.03  
% 2.30/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.30/1.03  ------ Proving...
% 2.30/1.03  ------ Problem Properties 
% 2.30/1.03  
% 2.30/1.03  
% 2.30/1.03  clauses                                 10
% 2.30/1.03  conjectures                             3
% 2.30/1.03  EPR                                     4
% 2.30/1.03  Horn                                    10
% 2.30/1.03  unary                                   4
% 2.30/1.03  binary                                  1
% 2.30/1.03  lits                                    21
% 2.30/1.03  lits eq                                 5
% 2.30/1.03  fd_pure                                 0
% 2.30/1.03  fd_pseudo                               0
% 2.30/1.03  fd_cond                                 0
% 2.30/1.03  fd_pseudo_cond                          1
% 2.30/1.03  AC symbols                              0
% 2.30/1.03  
% 2.30/1.03  ------ Schedule dynamic 5 is on 
% 2.30/1.03  
% 2.30/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.30/1.03  
% 2.30/1.03  
% 2.30/1.03  ------ 
% 2.30/1.03  Current options:
% 2.30/1.03  ------ 
% 2.30/1.03  
% 2.30/1.03  ------ Input Options
% 2.30/1.03  
% 2.30/1.03  --out_options                           all
% 2.30/1.03  --tptp_safe_out                         true
% 2.30/1.03  --problem_path                          ""
% 2.30/1.03  --include_path                          ""
% 2.30/1.03  --clausifier                            res/vclausify_rel
% 2.30/1.03  --clausifier_options                    --mode clausify
% 2.30/1.03  --stdin                                 false
% 2.30/1.03  --stats_out                             all
% 2.30/1.03  
% 2.30/1.03  ------ General Options
% 2.30/1.03  
% 2.30/1.03  --fof                                   false
% 2.30/1.03  --time_out_real                         305.
% 2.30/1.03  --time_out_virtual                      -1.
% 2.30/1.03  --symbol_type_check                     false
% 2.30/1.03  --clausify_out                          false
% 2.30/1.03  --sig_cnt_out                           false
% 2.30/1.03  --trig_cnt_out                          false
% 2.30/1.03  --trig_cnt_out_tolerance                1.
% 2.30/1.03  --trig_cnt_out_sk_spl                   false
% 2.30/1.03  --abstr_cl_out                          false
% 2.30/1.03  
% 2.30/1.03  ------ Global Options
% 2.30/1.03  
% 2.30/1.03  --schedule                              default
% 2.30/1.03  --add_important_lit                     false
% 2.30/1.03  --prop_solver_per_cl                    1000
% 2.30/1.03  --min_unsat_core                        false
% 2.30/1.03  --soft_assumptions                      false
% 2.30/1.03  --soft_lemma_size                       3
% 2.30/1.03  --prop_impl_unit_size                   0
% 2.30/1.03  --prop_impl_unit                        []
% 2.30/1.03  --share_sel_clauses                     true
% 2.30/1.03  --reset_solvers                         false
% 2.30/1.03  --bc_imp_inh                            [conj_cone]
% 2.30/1.03  --conj_cone_tolerance                   3.
% 2.30/1.03  --extra_neg_conj                        none
% 2.30/1.03  --large_theory_mode                     true
% 2.30/1.03  --prolific_symb_bound                   200
% 2.30/1.03  --lt_threshold                          2000
% 2.30/1.03  --clause_weak_htbl                      true
% 2.30/1.03  --gc_record_bc_elim                     false
% 2.30/1.03  
% 2.30/1.03  ------ Preprocessing Options
% 2.30/1.03  
% 2.30/1.03  --preprocessing_flag                    true
% 2.30/1.03  --time_out_prep_mult                    0.1
% 2.30/1.03  --splitting_mode                        input
% 2.30/1.03  --splitting_grd                         true
% 2.30/1.03  --splitting_cvd                         false
% 2.30/1.03  --splitting_cvd_svl                     false
% 2.30/1.03  --splitting_nvd                         32
% 2.30/1.03  --sub_typing                            true
% 2.30/1.03  --prep_gs_sim                           true
% 2.30/1.03  --prep_unflatten                        true
% 2.30/1.03  --prep_res_sim                          true
% 2.30/1.03  --prep_upred                            true
% 2.30/1.03  --prep_sem_filter                       exhaustive
% 2.30/1.03  --prep_sem_filter_out                   false
% 2.30/1.03  --pred_elim                             true
% 2.30/1.03  --res_sim_input                         true
% 2.30/1.03  --eq_ax_congr_red                       true
% 2.30/1.03  --pure_diseq_elim                       true
% 2.30/1.03  --brand_transform                       false
% 2.30/1.03  --non_eq_to_eq                          false
% 2.30/1.03  --prep_def_merge                        true
% 2.30/1.03  --prep_def_merge_prop_impl              false
% 2.30/1.03  --prep_def_merge_mbd                    true
% 2.30/1.03  --prep_def_merge_tr_red                 false
% 2.30/1.03  --prep_def_merge_tr_cl                  false
% 2.30/1.03  --smt_preprocessing                     true
% 2.30/1.03  --smt_ac_axioms                         fast
% 2.30/1.03  --preprocessed_out                      false
% 2.30/1.03  --preprocessed_stats                    false
% 2.30/1.03  
% 2.30/1.03  ------ Abstraction refinement Options
% 2.30/1.03  
% 2.30/1.03  --abstr_ref                             []
% 2.30/1.03  --abstr_ref_prep                        false
% 2.30/1.03  --abstr_ref_until_sat                   false
% 2.30/1.03  --abstr_ref_sig_restrict                funpre
% 2.30/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.30/1.03  --abstr_ref_under                       []
% 2.30/1.03  
% 2.30/1.03  ------ SAT Options
% 2.30/1.03  
% 2.30/1.03  --sat_mode                              false
% 2.30/1.03  --sat_fm_restart_options                ""
% 2.30/1.03  --sat_gr_def                            false
% 2.30/1.03  --sat_epr_types                         true
% 2.30/1.03  --sat_non_cyclic_types                  false
% 2.30/1.03  --sat_finite_models                     false
% 2.30/1.03  --sat_fm_lemmas                         false
% 2.30/1.03  --sat_fm_prep                           false
% 2.30/1.03  --sat_fm_uc_incr                        true
% 2.30/1.03  --sat_out_model                         small
% 2.30/1.03  --sat_out_clauses                       false
% 2.30/1.03  
% 2.30/1.03  ------ QBF Options
% 2.30/1.03  
% 2.30/1.03  --qbf_mode                              false
% 2.30/1.03  --qbf_elim_univ                         false
% 2.30/1.03  --qbf_dom_inst                          none
% 2.30/1.03  --qbf_dom_pre_inst                      false
% 2.30/1.03  --qbf_sk_in                             false
% 2.30/1.03  --qbf_pred_elim                         true
% 2.30/1.03  --qbf_split                             512
% 2.30/1.03  
% 2.30/1.03  ------ BMC1 Options
% 2.30/1.03  
% 2.30/1.03  --bmc1_incremental                      false
% 2.30/1.03  --bmc1_axioms                           reachable_all
% 2.30/1.03  --bmc1_min_bound                        0
% 2.30/1.03  --bmc1_max_bound                        -1
% 2.30/1.03  --bmc1_max_bound_default                -1
% 2.30/1.03  --bmc1_symbol_reachability              true
% 2.30/1.03  --bmc1_property_lemmas                  false
% 2.30/1.03  --bmc1_k_induction                      false
% 2.30/1.03  --bmc1_non_equiv_states                 false
% 2.30/1.03  --bmc1_deadlock                         false
% 2.30/1.03  --bmc1_ucm                              false
% 2.30/1.03  --bmc1_add_unsat_core                   none
% 2.30/1.03  --bmc1_unsat_core_children              false
% 2.30/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.30/1.03  --bmc1_out_stat                         full
% 2.30/1.03  --bmc1_ground_init                      false
% 2.30/1.03  --bmc1_pre_inst_next_state              false
% 2.30/1.03  --bmc1_pre_inst_state                   false
% 2.30/1.03  --bmc1_pre_inst_reach_state             false
% 2.30/1.03  --bmc1_out_unsat_core                   false
% 2.30/1.03  --bmc1_aig_witness_out                  false
% 2.30/1.03  --bmc1_verbose                          false
% 2.30/1.03  --bmc1_dump_clauses_tptp                false
% 2.30/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.30/1.03  --bmc1_dump_file                        -
% 2.30/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.30/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.30/1.03  --bmc1_ucm_extend_mode                  1
% 2.30/1.03  --bmc1_ucm_init_mode                    2
% 2.30/1.03  --bmc1_ucm_cone_mode                    none
% 2.30/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.30/1.03  --bmc1_ucm_relax_model                  4
% 2.30/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.30/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.30/1.03  --bmc1_ucm_layered_model                none
% 2.30/1.03  --bmc1_ucm_max_lemma_size               10
% 2.30/1.03  
% 2.30/1.03  ------ AIG Options
% 2.30/1.03  
% 2.30/1.03  --aig_mode                              false
% 2.30/1.03  
% 2.30/1.03  ------ Instantiation Options
% 2.30/1.03  
% 2.30/1.03  --instantiation_flag                    true
% 2.30/1.03  --inst_sos_flag                         false
% 2.30/1.03  --inst_sos_phase                        true
% 2.30/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.30/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.30/1.03  --inst_lit_sel_side                     none
% 2.30/1.03  --inst_solver_per_active                1400
% 2.30/1.03  --inst_solver_calls_frac                1.
% 2.30/1.03  --inst_passive_queue_type               priority_queues
% 2.30/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.30/1.03  --inst_passive_queues_freq              [25;2]
% 2.30/1.03  --inst_dismatching                      true
% 2.30/1.03  --inst_eager_unprocessed_to_passive     true
% 2.30/1.03  --inst_prop_sim_given                   true
% 2.30/1.03  --inst_prop_sim_new                     false
% 2.30/1.03  --inst_subs_new                         false
% 2.30/1.03  --inst_eq_res_simp                      false
% 2.30/1.03  --inst_subs_given                       false
% 2.30/1.03  --inst_orphan_elimination               true
% 2.30/1.03  --inst_learning_loop_flag               true
% 2.30/1.03  --inst_learning_start                   3000
% 2.30/1.03  --inst_learning_factor                  2
% 2.30/1.03  --inst_start_prop_sim_after_learn       3
% 2.30/1.03  --inst_sel_renew                        solver
% 2.30/1.03  --inst_lit_activity_flag                true
% 2.30/1.03  --inst_restr_to_given                   false
% 2.30/1.03  --inst_activity_threshold               500
% 2.30/1.03  --inst_out_proof                        true
% 2.30/1.03  
% 2.30/1.03  ------ Resolution Options
% 2.30/1.03  
% 2.30/1.03  --resolution_flag                       false
% 2.30/1.03  --res_lit_sel                           adaptive
% 2.30/1.03  --res_lit_sel_side                      none
% 2.30/1.03  --res_ordering                          kbo
% 2.30/1.03  --res_to_prop_solver                    active
% 2.30/1.03  --res_prop_simpl_new                    false
% 2.30/1.03  --res_prop_simpl_given                  true
% 2.30/1.03  --res_passive_queue_type                priority_queues
% 2.30/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.30/1.03  --res_passive_queues_freq               [15;5]
% 2.30/1.03  --res_forward_subs                      full
% 2.30/1.03  --res_backward_subs                     full
% 2.30/1.03  --res_forward_subs_resolution           true
% 2.30/1.03  --res_backward_subs_resolution          true
% 2.30/1.03  --res_orphan_elimination                true
% 2.30/1.03  --res_time_limit                        2.
% 2.30/1.03  --res_out_proof                         true
% 2.30/1.03  
% 2.30/1.03  ------ Superposition Options
% 2.30/1.03  
% 2.30/1.03  --superposition_flag                    true
% 2.30/1.03  --sup_passive_queue_type                priority_queues
% 2.30/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.30/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.30/1.03  --demod_completeness_check              fast
% 2.30/1.03  --demod_use_ground                      true
% 2.30/1.03  --sup_to_prop_solver                    passive
% 2.30/1.03  --sup_prop_simpl_new                    true
% 2.30/1.03  --sup_prop_simpl_given                  true
% 2.30/1.03  --sup_fun_splitting                     false
% 2.30/1.03  --sup_smt_interval                      50000
% 2.30/1.03  
% 2.30/1.03  ------ Superposition Simplification Setup
% 2.30/1.03  
% 2.30/1.03  --sup_indices_passive                   []
% 2.30/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.30/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.30/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.30/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.30/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.30/1.03  --sup_full_bw                           [BwDemod]
% 2.30/1.03  --sup_immed_triv                        [TrivRules]
% 2.30/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.30/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.30/1.03  --sup_immed_bw_main                     []
% 2.30/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.30/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.30/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.30/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.30/1.03  
% 2.30/1.03  ------ Combination Options
% 2.30/1.03  
% 2.30/1.03  --comb_res_mult                         3
% 2.30/1.03  --comb_sup_mult                         2
% 2.30/1.03  --comb_inst_mult                        10
% 2.30/1.03  
% 2.30/1.03  ------ Debug Options
% 2.30/1.03  
% 2.30/1.03  --dbg_backtrace                         false
% 2.30/1.03  --dbg_dump_prop_clauses                 false
% 2.30/1.03  --dbg_dump_prop_clauses_file            -
% 2.30/1.03  --dbg_out_stat                          false
% 2.30/1.03  
% 2.30/1.03  
% 2.30/1.03  
% 2.30/1.03  
% 2.30/1.03  ------ Proving...
% 2.30/1.03  
% 2.30/1.03  
% 2.30/1.03  % SZS status Theorem for theBenchmark.p
% 2.30/1.03  
% 2.30/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.30/1.03  
% 2.30/1.03  fof(f7,conjecture,(
% 2.30/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 2.30/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.30/1.03  
% 2.30/1.03  fof(f8,negated_conjecture,(
% 2.30/1.03    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 2.30/1.03    inference(negated_conjecture,[],[f7])).
% 2.30/1.03  
% 2.30/1.03  fof(f16,plain,(
% 2.30/1.03    ? [X0] : (? [X1] : (k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.30/1.03    inference(ennf_transformation,[],[f8])).
% 2.30/1.03  
% 2.30/1.03  fof(f20,plain,(
% 2.30/1.03    ( ! [X0] : (? [X1] : (k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0)) & v1_relat_1(X1)) => (k2_relat_1(k5_relat_1(X0,sK1)) != k9_relat_1(sK1,k2_relat_1(X0)) & v1_relat_1(sK1))) )),
% 2.30/1.03    introduced(choice_axiom,[])).
% 2.30/1.03  
% 2.30/1.03  fof(f19,plain,(
% 2.30/1.03    ? [X0] : (? [X1] : (k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 2.30/1.03    introduced(choice_axiom,[])).
% 2.30/1.03  
% 2.30/1.03  fof(f21,plain,(
% 2.30/1.03    (k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 2.30/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f20,f19])).
% 2.30/1.03  
% 2.30/1.03  fof(f31,plain,(
% 2.30/1.03    v1_relat_1(sK1)),
% 2.30/1.03    inference(cnf_transformation,[],[f21])).
% 2.30/1.03  
% 2.30/1.03  fof(f30,plain,(
% 2.30/1.03    v1_relat_1(sK0)),
% 2.30/1.03    inference(cnf_transformation,[],[f21])).
% 2.30/1.03  
% 2.30/1.03  fof(f5,axiom,(
% 2.30/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 2.30/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.30/1.03  
% 2.30/1.03  fof(f13,plain,(
% 2.30/1.03    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.30/1.03    inference(ennf_transformation,[],[f5])).
% 2.30/1.03  
% 2.30/1.03  fof(f28,plain,(
% 2.30/1.03    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.30/1.03    inference(cnf_transformation,[],[f13])).
% 2.30/1.03  
% 2.30/1.03  fof(f6,axiom,(
% 2.30/1.03    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 2.30/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.30/1.03  
% 2.30/1.03  fof(f14,plain,(
% 2.30/1.03    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.30/1.03    inference(ennf_transformation,[],[f6])).
% 2.30/1.03  
% 2.30/1.03  fof(f15,plain,(
% 2.30/1.03    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.30/1.03    inference(flattening,[],[f14])).
% 2.30/1.03  
% 2.30/1.03  fof(f29,plain,(
% 2.30/1.03    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.30/1.03    inference(cnf_transformation,[],[f15])).
% 2.30/1.03  
% 2.30/1.03  fof(f2,axiom,(
% 2.30/1.03    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 2.30/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.30/1.03  
% 2.30/1.03  fof(f9,plain,(
% 2.30/1.03    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 2.30/1.03    inference(ennf_transformation,[],[f2])).
% 2.30/1.03  
% 2.30/1.03  fof(f10,plain,(
% 2.30/1.03    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 2.30/1.03    inference(flattening,[],[f9])).
% 2.30/1.03  
% 2.30/1.03  fof(f25,plain,(
% 2.30/1.03    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.30/1.03    inference(cnf_transformation,[],[f10])).
% 2.30/1.03  
% 2.30/1.03  fof(f3,axiom,(
% 2.30/1.03    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.30/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.30/1.03  
% 2.30/1.03  fof(f11,plain,(
% 2.30/1.03    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.30/1.03    inference(ennf_transformation,[],[f3])).
% 2.30/1.03  
% 2.30/1.03  fof(f26,plain,(
% 2.30/1.03    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.30/1.03    inference(cnf_transformation,[],[f11])).
% 2.30/1.03  
% 2.30/1.03  fof(f4,axiom,(
% 2.30/1.03    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0)))),
% 2.30/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.30/1.03  
% 2.30/1.03  fof(f12,plain,(
% 2.30/1.03    ! [X0,X1] : (! [X2] : (k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 2.30/1.03    inference(ennf_transformation,[],[f4])).
% 2.30/1.03  
% 2.30/1.03  fof(f27,plain,(
% 2.30/1.03    ( ! [X2,X0,X1] : (k9_relat_1(X2,k9_relat_1(X1,X0)) = k9_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 2.30/1.03    inference(cnf_transformation,[],[f12])).
% 2.30/1.03  
% 2.30/1.03  fof(f1,axiom,(
% 2.30/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.30/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.30/1.03  
% 2.30/1.03  fof(f17,plain,(
% 2.30/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.30/1.03    inference(nnf_transformation,[],[f1])).
% 2.30/1.03  
% 2.30/1.03  fof(f18,plain,(
% 2.30/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.30/1.03    inference(flattening,[],[f17])).
% 2.30/1.03  
% 2.30/1.03  fof(f23,plain,(
% 2.30/1.03    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.30/1.03    inference(cnf_transformation,[],[f18])).
% 2.30/1.03  
% 2.30/1.03  fof(f33,plain,(
% 2.30/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.30/1.03    inference(equality_resolution,[],[f23])).
% 2.30/1.03  
% 2.30/1.03  fof(f32,plain,(
% 2.30/1.03    k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))),
% 2.30/1.03    inference(cnf_transformation,[],[f21])).
% 2.30/1.03  
% 2.30/1.03  cnf(c_9,negated_conjecture,
% 2.30/1.03      ( v1_relat_1(sK1) ),
% 2.30/1.03      inference(cnf_transformation,[],[f31]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_347,plain,
% 2.30/1.03      ( v1_relat_1(sK1) = iProver_top ),
% 2.30/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_10,negated_conjecture,
% 2.30/1.03      ( v1_relat_1(sK0) ),
% 2.30/1.03      inference(cnf_transformation,[],[f30]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_346,plain,
% 2.30/1.03      ( v1_relat_1(sK0) = iProver_top ),
% 2.30/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_6,plain,
% 2.30/1.03      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
% 2.30/1.03      | ~ v1_relat_1(X1)
% 2.30/1.03      | ~ v1_relat_1(X0) ),
% 2.30/1.03      inference(cnf_transformation,[],[f28]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_349,plain,
% 2.30/1.03      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 2.30/1.03      | v1_relat_1(X0) != iProver_top
% 2.30/1.03      | v1_relat_1(X1) != iProver_top ),
% 2.30/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_7,plain,
% 2.30/1.03      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 2.30/1.03      | ~ v1_relat_1(X0)
% 2.30/1.03      | k7_relat_1(X0,X1) = X0 ),
% 2.30/1.03      inference(cnf_transformation,[],[f29]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_348,plain,
% 2.30/1.03      ( k7_relat_1(X0,X1) = X0
% 2.30/1.03      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 2.30/1.03      | v1_relat_1(X0) != iProver_top ),
% 2.30/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_821,plain,
% 2.30/1.03      ( k7_relat_1(k5_relat_1(X0,X1),k1_relat_1(X0)) = k5_relat_1(X0,X1)
% 2.30/1.03      | v1_relat_1(X0) != iProver_top
% 2.30/1.03      | v1_relat_1(X1) != iProver_top
% 2.30/1.03      | v1_relat_1(k5_relat_1(X0,X1)) != iProver_top ),
% 2.30/1.03      inference(superposition,[status(thm)],[c_349,c_348]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_3,plain,
% 2.30/1.03      ( ~ v1_relat_1(X0)
% 2.30/1.03      | ~ v1_relat_1(X1)
% 2.30/1.03      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 2.30/1.03      inference(cnf_transformation,[],[f25]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_352,plain,
% 2.30/1.03      ( v1_relat_1(X0) != iProver_top
% 2.30/1.03      | v1_relat_1(X1) != iProver_top
% 2.30/1.03      | v1_relat_1(k5_relat_1(X1,X0)) = iProver_top ),
% 2.30/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_2782,plain,
% 2.30/1.03      ( k7_relat_1(k5_relat_1(X0,X1),k1_relat_1(X0)) = k5_relat_1(X0,X1)
% 2.30/1.03      | v1_relat_1(X0) != iProver_top
% 2.30/1.03      | v1_relat_1(X1) != iProver_top ),
% 2.30/1.03      inference(forward_subsumption_resolution,
% 2.30/1.03                [status(thm)],
% 2.30/1.03                [c_821,c_352]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_2788,plain,
% 2.30/1.03      ( k7_relat_1(k5_relat_1(sK0,X0),k1_relat_1(sK0)) = k5_relat_1(sK0,X0)
% 2.30/1.03      | v1_relat_1(X0) != iProver_top ),
% 2.30/1.03      inference(superposition,[status(thm)],[c_346,c_2782]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_3032,plain,
% 2.30/1.03      ( k7_relat_1(k5_relat_1(sK0,sK1),k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) ),
% 2.30/1.03      inference(superposition,[status(thm)],[c_347,c_2788]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_4,plain,
% 2.30/1.03      ( ~ v1_relat_1(X0)
% 2.30/1.03      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.30/1.03      inference(cnf_transformation,[],[f26]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_351,plain,
% 2.30/1.03      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 2.30/1.03      | v1_relat_1(X0) != iProver_top ),
% 2.30/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_694,plain,
% 2.30/1.03      ( k2_relat_1(k7_relat_1(k5_relat_1(X0,X1),X2)) = k9_relat_1(k5_relat_1(X0,X1),X2)
% 2.30/1.03      | v1_relat_1(X1) != iProver_top
% 2.30/1.03      | v1_relat_1(X0) != iProver_top ),
% 2.30/1.03      inference(superposition,[status(thm)],[c_352,c_351]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1619,plain,
% 2.30/1.03      ( k2_relat_1(k7_relat_1(k5_relat_1(sK0,X0),X1)) = k9_relat_1(k5_relat_1(sK0,X0),X1)
% 2.30/1.03      | v1_relat_1(X0) != iProver_top ),
% 2.30/1.03      inference(superposition,[status(thm)],[c_346,c_694]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1833,plain,
% 2.30/1.03      ( k2_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X0)) = k9_relat_1(k5_relat_1(sK0,sK1),X0) ),
% 2.30/1.03      inference(superposition,[status(thm)],[c_347,c_1619]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_5,plain,
% 2.30/1.03      ( ~ v1_relat_1(X0)
% 2.30/1.03      | ~ v1_relat_1(X1)
% 2.30/1.03      | k9_relat_1(k5_relat_1(X0,X1),X2) = k9_relat_1(X1,k9_relat_1(X0,X2)) ),
% 2.30/1.03      inference(cnf_transformation,[],[f27]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_350,plain,
% 2.30/1.03      ( k9_relat_1(k5_relat_1(X0,X1),X2) = k9_relat_1(X1,k9_relat_1(X0,X2))
% 2.30/1.03      | v1_relat_1(X0) != iProver_top
% 2.30/1.03      | v1_relat_1(X1) != iProver_top ),
% 2.30/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_850,plain,
% 2.30/1.03      ( k9_relat_1(X0,k9_relat_1(sK0,X1)) = k9_relat_1(k5_relat_1(sK0,X0),X1)
% 2.30/1.03      | v1_relat_1(X0) != iProver_top ),
% 2.30/1.03      inference(superposition,[status(thm)],[c_346,c_350]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1052,plain,
% 2.30/1.03      ( k9_relat_1(k5_relat_1(sK0,sK1),X0) = k9_relat_1(sK1,k9_relat_1(sK0,X0)) ),
% 2.30/1.03      inference(superposition,[status(thm)],[c_347,c_850]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1839,plain,
% 2.30/1.03      ( k2_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X0)) = k9_relat_1(sK1,k9_relat_1(sK0,X0)) ),
% 2.30/1.03      inference(light_normalisation,[status(thm)],[c_1833,c_1052]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_3048,plain,
% 2.30/1.03      ( k9_relat_1(sK1,k9_relat_1(sK0,k1_relat_1(sK0))) = k2_relat_1(k5_relat_1(sK0,sK1)) ),
% 2.30/1.03      inference(superposition,[status(thm)],[c_3032,c_1839]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1,plain,
% 2.30/1.03      ( r1_tarski(X0,X0) ),
% 2.30/1.03      inference(cnf_transformation,[],[f33]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_353,plain,
% 2.30/1.03      ( r1_tarski(X0,X0) = iProver_top ),
% 2.30/1.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_686,plain,
% 2.30/1.03      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 2.30/1.03      | v1_relat_1(X0) != iProver_top ),
% 2.30/1.03      inference(superposition,[status(thm)],[c_353,c_348]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1390,plain,
% 2.30/1.03      ( k7_relat_1(sK0,k1_relat_1(sK0)) = sK0 ),
% 2.30/1.03      inference(superposition,[status(thm)],[c_346,c_686]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_523,plain,
% 2.30/1.03      ( k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0) ),
% 2.30/1.03      inference(superposition,[status(thm)],[c_346,c_351]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_1495,plain,
% 2.30/1.03      ( k9_relat_1(sK0,k1_relat_1(sK0)) = k2_relat_1(sK0) ),
% 2.30/1.03      inference(superposition,[status(thm)],[c_1390,c_523]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_3049,plain,
% 2.30/1.03      ( k9_relat_1(sK1,k2_relat_1(sK0)) = k2_relat_1(k5_relat_1(sK0,sK1)) ),
% 2.30/1.03      inference(light_normalisation,[status(thm)],[c_3048,c_1495]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_8,negated_conjecture,
% 2.30/1.03      ( k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) ),
% 2.30/1.03      inference(cnf_transformation,[],[f32]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_17799,plain,
% 2.30/1.03      ( k2_relat_1(k5_relat_1(sK0,sK1)) != k2_relat_1(k5_relat_1(sK0,sK1)) ),
% 2.30/1.03      inference(demodulation,[status(thm)],[c_3049,c_8]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_176,plain,( X0 = X0 ),theory(equality) ).
% 2.30/1.03  
% 2.30/1.03  cnf(c_785,plain,
% 2.30/1.03      ( k2_relat_1(k5_relat_1(sK0,sK1)) = k2_relat_1(k5_relat_1(sK0,sK1)) ),
% 2.30/1.03      inference(instantiation,[status(thm)],[c_176]) ).
% 2.30/1.03  
% 2.30/1.03  cnf(contradiction,plain,
% 2.30/1.03      ( $false ),
% 2.30/1.03      inference(minisat,[status(thm)],[c_17799,c_785]) ).
% 2.30/1.03  
% 2.30/1.03  
% 2.30/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.30/1.03  
% 2.30/1.03  ------                               Statistics
% 2.30/1.03  
% 2.30/1.03  ------ General
% 2.30/1.03  
% 2.30/1.03  abstr_ref_over_cycles:                  0
% 2.30/1.03  abstr_ref_under_cycles:                 0
% 2.30/1.03  gc_basic_clause_elim:                   0
% 2.30/1.03  forced_gc_time:                         0
% 2.30/1.03  parsing_time:                           0.026
% 2.30/1.03  unif_index_cands_time:                  0.
% 2.30/1.03  unif_index_add_time:                    0.
% 2.30/1.03  orderings_time:                         0.
% 2.30/1.03  out_proof_time:                         0.008
% 2.30/1.03  total_time:                             0.507
% 2.30/1.03  num_of_symbols:                         40
% 2.30/1.03  num_of_terms:                           9676
% 2.30/1.03  
% 2.30/1.03  ------ Preprocessing
% 2.30/1.03  
% 2.30/1.03  num_of_splits:                          0
% 2.30/1.03  num_of_split_atoms:                     0
% 2.30/1.03  num_of_reused_defs:                     0
% 2.30/1.03  num_eq_ax_congr_red:                    6
% 2.30/1.03  num_of_sem_filtered_clauses:            1
% 2.30/1.03  num_of_subtypes:                        0
% 2.30/1.03  monotx_restored_types:                  0
% 2.30/1.03  sat_num_of_epr_types:                   0
% 2.30/1.03  sat_num_of_non_cyclic_types:            0
% 2.30/1.03  sat_guarded_non_collapsed_types:        0
% 2.30/1.03  num_pure_diseq_elim:                    0
% 2.30/1.03  simp_replaced_by:                       0
% 2.30/1.03  res_preprocessed:                       57
% 2.30/1.03  prep_upred:                             0
% 2.30/1.03  prep_unflattend:                        0
% 2.30/1.03  smt_new_axioms:                         0
% 2.30/1.03  pred_elim_cands:                        2
% 2.30/1.03  pred_elim:                              0
% 2.30/1.03  pred_elim_cl:                           0
% 2.30/1.03  pred_elim_cycles:                       2
% 2.30/1.03  merged_defs:                            0
% 2.30/1.03  merged_defs_ncl:                        0
% 2.30/1.03  bin_hyper_res:                          0
% 2.30/1.03  prep_cycles:                            4
% 2.30/1.03  pred_elim_time:                         0.
% 2.30/1.03  splitting_time:                         0.
% 2.30/1.03  sem_filter_time:                        0.
% 2.30/1.03  monotx_time:                            0.001
% 2.30/1.03  subtype_inf_time:                       0.
% 2.30/1.03  
% 2.30/1.03  ------ Problem properties
% 2.30/1.03  
% 2.30/1.03  clauses:                                10
% 2.30/1.03  conjectures:                            3
% 2.30/1.03  epr:                                    4
% 2.30/1.03  horn:                                   10
% 2.30/1.03  ground:                                 3
% 2.30/1.03  unary:                                  4
% 2.30/1.03  binary:                                 1
% 2.30/1.03  lits:                                   21
% 2.30/1.03  lits_eq:                                5
% 2.30/1.03  fd_pure:                                0
% 2.30/1.03  fd_pseudo:                              0
% 2.30/1.03  fd_cond:                                0
% 2.30/1.03  fd_pseudo_cond:                         1
% 2.30/1.03  ac_symbols:                             0
% 2.30/1.03  
% 2.30/1.03  ------ Propositional Solver
% 2.30/1.03  
% 2.30/1.03  prop_solver_calls:                      35
% 2.30/1.03  prop_fast_solver_calls:                 590
% 2.30/1.03  smt_solver_calls:                       0
% 2.30/1.03  smt_fast_solver_calls:                  0
% 2.30/1.03  prop_num_of_clauses:                    4797
% 2.30/1.03  prop_preprocess_simplified:             10780
% 2.30/1.03  prop_fo_subsumed:                       0
% 2.30/1.03  prop_solver_time:                       0.
% 2.30/1.03  smt_solver_time:                        0.
% 2.30/1.03  smt_fast_solver_time:                   0.
% 2.30/1.03  prop_fast_solver_time:                  0.
% 2.30/1.03  prop_unsat_core_time:                   0.
% 2.30/1.03  
% 2.30/1.03  ------ QBF
% 2.30/1.03  
% 2.30/1.03  qbf_q_res:                              0
% 2.30/1.03  qbf_num_tautologies:                    0
% 2.30/1.03  qbf_prep_cycles:                        0
% 2.30/1.03  
% 2.30/1.03  ------ BMC1
% 2.30/1.03  
% 2.30/1.03  bmc1_current_bound:                     -1
% 2.30/1.03  bmc1_last_solved_bound:                 -1
% 2.30/1.03  bmc1_unsat_core_size:                   -1
% 2.30/1.03  bmc1_unsat_core_parents_size:           -1
% 2.30/1.03  bmc1_merge_next_fun:                    0
% 2.30/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.30/1.03  
% 2.30/1.03  ------ Instantiation
% 2.30/1.03  
% 2.30/1.03  inst_num_of_clauses:                    2057
% 2.30/1.03  inst_num_in_passive:                    309
% 2.30/1.03  inst_num_in_active:                     1001
% 2.30/1.03  inst_num_in_unprocessed:                747
% 2.30/1.03  inst_num_of_loops:                      1020
% 2.30/1.03  inst_num_of_learning_restarts:          0
% 2.30/1.03  inst_num_moves_active_passive:          12
% 2.30/1.03  inst_lit_activity:                      0
% 2.30/1.03  inst_lit_activity_moves:                0
% 2.30/1.03  inst_num_tautologies:                   0
% 2.30/1.03  inst_num_prop_implied:                  0
% 2.30/1.03  inst_num_existing_simplified:           0
% 2.30/1.03  inst_num_eq_res_simplified:             0
% 2.30/1.03  inst_num_child_elim:                    0
% 2.30/1.03  inst_num_of_dismatching_blockings:      1523
% 2.30/1.03  inst_num_of_non_proper_insts:           4491
% 2.30/1.03  inst_num_of_duplicates:                 0
% 2.30/1.03  inst_inst_num_from_inst_to_res:         0
% 2.30/1.03  inst_dismatching_checking_time:         0.
% 2.30/1.03  
% 2.30/1.03  ------ Resolution
% 2.30/1.03  
% 2.30/1.03  res_num_of_clauses:                     0
% 2.30/1.03  res_num_in_passive:                     0
% 2.30/1.03  res_num_in_active:                      0
% 2.30/1.03  res_num_of_loops:                       61
% 2.30/1.03  res_forward_subset_subsumed:            718
% 2.30/1.03  res_backward_subset_subsumed:           2
% 2.30/1.03  res_forward_subsumed:                   0
% 2.30/1.03  res_backward_subsumed:                  0
% 2.30/1.03  res_forward_subsumption_resolution:     0
% 2.30/1.03  res_backward_subsumption_resolution:    0
% 2.30/1.03  res_clause_to_clause_subsumption:       1490
% 2.30/1.03  res_orphan_elimination:                 0
% 2.30/1.03  res_tautology_del:                      427
% 2.30/1.03  res_num_eq_res_simplified:              0
% 2.30/1.03  res_num_sel_changes:                    0
% 2.30/1.03  res_moves_from_active_to_pass:          0
% 2.30/1.03  
% 2.30/1.03  ------ Superposition
% 2.30/1.03  
% 2.30/1.03  sup_time_total:                         0.
% 2.30/1.03  sup_time_generating:                    0.
% 2.30/1.03  sup_time_sim_full:                      0.
% 2.30/1.03  sup_time_sim_immed:                     0.
% 2.30/1.03  
% 2.30/1.03  sup_num_of_clauses:                     306
% 2.30/1.03  sup_num_in_active:                      190
% 2.30/1.03  sup_num_in_passive:                     116
% 2.30/1.03  sup_num_of_loops:                       202
% 2.30/1.03  sup_fw_superposition:                   283
% 2.30/1.03  sup_bw_superposition:                   21
% 2.30/1.03  sup_immediate_simplified:               61
% 2.30/1.03  sup_given_eliminated:                   0
% 2.30/1.03  comparisons_done:                       0
% 2.30/1.03  comparisons_avoided:                    0
% 2.30/1.03  
% 2.30/1.03  ------ Simplifications
% 2.30/1.03  
% 2.30/1.03  
% 2.30/1.03  sim_fw_subset_subsumed:                 0
% 2.30/1.03  sim_bw_subset_subsumed:                 0
% 2.30/1.03  sim_fw_subsumed:                        0
% 2.30/1.03  sim_bw_subsumed:                        0
% 2.30/1.03  sim_fw_subsumption_res:                 1
% 2.30/1.03  sim_bw_subsumption_res:                 0
% 2.30/1.03  sim_tautology_del:                      0
% 2.30/1.03  sim_eq_tautology_del:                   1
% 2.30/1.03  sim_eq_res_simp:                        0
% 2.30/1.03  sim_fw_demodulated:                     17
% 2.30/1.03  sim_bw_demodulated:                     12
% 2.30/1.03  sim_light_normalised:                   44
% 2.30/1.03  sim_joinable_taut:                      0
% 2.30/1.03  sim_joinable_simp:                      0
% 2.30/1.03  sim_ac_normalised:                      0
% 2.30/1.03  sim_smt_subsumption:                    0
% 2.30/1.03  
%------------------------------------------------------------------------------
