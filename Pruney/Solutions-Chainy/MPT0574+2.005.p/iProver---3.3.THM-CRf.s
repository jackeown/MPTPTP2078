%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:47 EST 2020

% Result     : Theorem 11.71s
% Output     : CNFRefutation 11.71s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 112 expanded)
%              Number of clauses        :   35 (  38 expanded)
%              Number of leaves         :   11 (  24 expanded)
%              Depth                    :   13
%              Number of atoms          :  147 ( 224 expanded)
%              Number of equality atoms :   58 (  79 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f22])).

fof(f36,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f29,f33])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f24,f33])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f30,f33])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f31,f33])).

fof(f27,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f35,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) = k10_relat_1(X2,k3_tarski(k2_tarski(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f34,f33,f33])).

fof(f37,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_448,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_455,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_453,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1145,plain,
    ( r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_455,c_453])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_454,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2486,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X2,X0)),X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1145,c_454])).

cnf(c_0,plain,
    ( k3_tarski(k2_tarski(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_6,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_452,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_990,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_452])).

cnf(c_24854,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_tarski(k2_tarski(X1,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2486,c_990])).

cnf(c_8,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_7,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_451,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_869,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_451])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_456,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1351,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = X1
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_869,c_456])).

cnf(c_5647,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = X1
    | r1_tarski(k3_tarski(k2_tarski(X1,X0)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_1351])).

cnf(c_44290,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_24854,c_5647])).

cnf(c_45463,plain,
    ( k3_tarski(k2_tarski(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_448,c_44290])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_447,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k2_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,X2))) = k10_relat_1(X0,k3_tarski(k2_tarski(X1,X2))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_450,plain,
    ( k3_tarski(k2_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,X2))) = k10_relat_1(X0,k3_tarski(k2_tarski(X1,X2)))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1140,plain,
    ( k3_tarski(k2_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) = k10_relat_1(sK2,k3_tarski(k2_tarski(X0,X1))) ),
    inference(superposition,[status(thm)],[c_447,c_450])).

cnf(c_2763,plain,
    ( r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,k3_tarski(k2_tarski(X0,X1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1140,c_451])).

cnf(c_45936,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_45463,c_2763])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_15,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_45936,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:23:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.71/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.71/2.00  
% 11.71/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.71/2.00  
% 11.71/2.00  ------  iProver source info
% 11.71/2.00  
% 11.71/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.71/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.71/2.00  git: non_committed_changes: false
% 11.71/2.00  git: last_make_outside_of_git: false
% 11.71/2.00  
% 11.71/2.00  ------ 
% 11.71/2.00  
% 11.71/2.00  ------ Input Options
% 11.71/2.00  
% 11.71/2.00  --out_options                           all
% 11.71/2.00  --tptp_safe_out                         true
% 11.71/2.00  --problem_path                          ""
% 11.71/2.00  --include_path                          ""
% 11.71/2.00  --clausifier                            res/vclausify_rel
% 11.71/2.00  --clausifier_options                    --mode clausify
% 11.71/2.00  --stdin                                 false
% 11.71/2.00  --stats_out                             sel
% 11.71/2.00  
% 11.71/2.00  ------ General Options
% 11.71/2.00  
% 11.71/2.00  --fof                                   false
% 11.71/2.00  --time_out_real                         604.99
% 11.71/2.00  --time_out_virtual                      -1.
% 11.71/2.00  --symbol_type_check                     false
% 11.71/2.00  --clausify_out                          false
% 11.71/2.00  --sig_cnt_out                           false
% 11.71/2.00  --trig_cnt_out                          false
% 11.71/2.00  --trig_cnt_out_tolerance                1.
% 11.71/2.00  --trig_cnt_out_sk_spl                   false
% 11.71/2.00  --abstr_cl_out                          false
% 11.71/2.00  
% 11.71/2.00  ------ Global Options
% 11.71/2.00  
% 11.71/2.00  --schedule                              none
% 11.71/2.00  --add_important_lit                     false
% 11.71/2.00  --prop_solver_per_cl                    1000
% 11.71/2.00  --min_unsat_core                        false
% 11.71/2.00  --soft_assumptions                      false
% 11.71/2.00  --soft_lemma_size                       3
% 11.71/2.00  --prop_impl_unit_size                   0
% 11.71/2.00  --prop_impl_unit                        []
% 11.71/2.00  --share_sel_clauses                     true
% 11.71/2.00  --reset_solvers                         false
% 11.71/2.00  --bc_imp_inh                            [conj_cone]
% 11.71/2.00  --conj_cone_tolerance                   3.
% 11.71/2.00  --extra_neg_conj                        none
% 11.71/2.00  --large_theory_mode                     true
% 11.71/2.00  --prolific_symb_bound                   200
% 11.71/2.00  --lt_threshold                          2000
% 11.71/2.00  --clause_weak_htbl                      true
% 11.71/2.00  --gc_record_bc_elim                     false
% 11.71/2.00  
% 11.71/2.00  ------ Preprocessing Options
% 11.71/2.00  
% 11.71/2.00  --preprocessing_flag                    true
% 11.71/2.00  --time_out_prep_mult                    0.1
% 11.71/2.00  --splitting_mode                        input
% 11.71/2.00  --splitting_grd                         true
% 11.71/2.00  --splitting_cvd                         false
% 11.71/2.00  --splitting_cvd_svl                     false
% 11.71/2.00  --splitting_nvd                         32
% 11.71/2.00  --sub_typing                            true
% 11.71/2.00  --prep_gs_sim                           false
% 11.71/2.00  --prep_unflatten                        true
% 11.71/2.00  --prep_res_sim                          true
% 11.71/2.00  --prep_upred                            true
% 11.71/2.00  --prep_sem_filter                       exhaustive
% 11.71/2.00  --prep_sem_filter_out                   false
% 11.71/2.00  --pred_elim                             false
% 11.71/2.00  --res_sim_input                         true
% 11.71/2.00  --eq_ax_congr_red                       true
% 11.71/2.00  --pure_diseq_elim                       true
% 11.71/2.00  --brand_transform                       false
% 11.71/2.00  --non_eq_to_eq                          false
% 11.71/2.00  --prep_def_merge                        true
% 11.71/2.00  --prep_def_merge_prop_impl              false
% 11.71/2.00  --prep_def_merge_mbd                    true
% 11.71/2.00  --prep_def_merge_tr_red                 false
% 11.71/2.00  --prep_def_merge_tr_cl                  false
% 11.71/2.00  --smt_preprocessing                     true
% 11.71/2.00  --smt_ac_axioms                         fast
% 11.71/2.00  --preprocessed_out                      false
% 11.71/2.00  --preprocessed_stats                    false
% 11.71/2.00  
% 11.71/2.00  ------ Abstraction refinement Options
% 11.71/2.00  
% 11.71/2.00  --abstr_ref                             []
% 11.71/2.00  --abstr_ref_prep                        false
% 11.71/2.00  --abstr_ref_until_sat                   false
% 11.71/2.00  --abstr_ref_sig_restrict                funpre
% 11.71/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.71/2.00  --abstr_ref_under                       []
% 11.71/2.00  
% 11.71/2.00  ------ SAT Options
% 11.71/2.00  
% 11.71/2.00  --sat_mode                              false
% 11.71/2.00  --sat_fm_restart_options                ""
% 11.71/2.00  --sat_gr_def                            false
% 11.71/2.00  --sat_epr_types                         true
% 11.71/2.00  --sat_non_cyclic_types                  false
% 11.71/2.00  --sat_finite_models                     false
% 11.71/2.00  --sat_fm_lemmas                         false
% 11.71/2.00  --sat_fm_prep                           false
% 11.71/2.00  --sat_fm_uc_incr                        true
% 11.71/2.00  --sat_out_model                         small
% 11.71/2.00  --sat_out_clauses                       false
% 11.71/2.00  
% 11.71/2.00  ------ QBF Options
% 11.71/2.00  
% 11.71/2.00  --qbf_mode                              false
% 11.71/2.00  --qbf_elim_univ                         false
% 11.71/2.00  --qbf_dom_inst                          none
% 11.71/2.00  --qbf_dom_pre_inst                      false
% 11.71/2.00  --qbf_sk_in                             false
% 11.71/2.00  --qbf_pred_elim                         true
% 11.71/2.00  --qbf_split                             512
% 11.71/2.00  
% 11.71/2.00  ------ BMC1 Options
% 11.71/2.00  
% 11.71/2.00  --bmc1_incremental                      false
% 11.71/2.00  --bmc1_axioms                           reachable_all
% 11.71/2.00  --bmc1_min_bound                        0
% 11.71/2.00  --bmc1_max_bound                        -1
% 11.71/2.00  --bmc1_max_bound_default                -1
% 11.71/2.00  --bmc1_symbol_reachability              true
% 11.71/2.00  --bmc1_property_lemmas                  false
% 11.71/2.00  --bmc1_k_induction                      false
% 11.71/2.00  --bmc1_non_equiv_states                 false
% 11.71/2.00  --bmc1_deadlock                         false
% 11.71/2.00  --bmc1_ucm                              false
% 11.71/2.00  --bmc1_add_unsat_core                   none
% 11.71/2.00  --bmc1_unsat_core_children              false
% 11.71/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.71/2.00  --bmc1_out_stat                         full
% 11.71/2.00  --bmc1_ground_init                      false
% 11.71/2.00  --bmc1_pre_inst_next_state              false
% 11.71/2.00  --bmc1_pre_inst_state                   false
% 11.71/2.00  --bmc1_pre_inst_reach_state             false
% 11.71/2.00  --bmc1_out_unsat_core                   false
% 11.71/2.00  --bmc1_aig_witness_out                  false
% 11.71/2.00  --bmc1_verbose                          false
% 11.71/2.00  --bmc1_dump_clauses_tptp                false
% 11.71/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.71/2.00  --bmc1_dump_file                        -
% 11.71/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.71/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.71/2.00  --bmc1_ucm_extend_mode                  1
% 11.71/2.00  --bmc1_ucm_init_mode                    2
% 11.71/2.00  --bmc1_ucm_cone_mode                    none
% 11.71/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.71/2.00  --bmc1_ucm_relax_model                  4
% 11.71/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.71/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.71/2.00  --bmc1_ucm_layered_model                none
% 11.71/2.00  --bmc1_ucm_max_lemma_size               10
% 11.71/2.00  
% 11.71/2.00  ------ AIG Options
% 11.71/2.00  
% 11.71/2.00  --aig_mode                              false
% 11.71/2.00  
% 11.71/2.00  ------ Instantiation Options
% 11.71/2.00  
% 11.71/2.00  --instantiation_flag                    true
% 11.71/2.00  --inst_sos_flag                         false
% 11.71/2.00  --inst_sos_phase                        true
% 11.71/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.71/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.71/2.00  --inst_lit_sel_side                     num_symb
% 11.71/2.00  --inst_solver_per_active                1400
% 11.71/2.00  --inst_solver_calls_frac                1.
% 11.71/2.00  --inst_passive_queue_type               priority_queues
% 11.71/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.71/2.00  --inst_passive_queues_freq              [25;2]
% 11.71/2.00  --inst_dismatching                      true
% 11.71/2.00  --inst_eager_unprocessed_to_passive     true
% 11.71/2.00  --inst_prop_sim_given                   true
% 11.71/2.00  --inst_prop_sim_new                     false
% 11.71/2.00  --inst_subs_new                         false
% 11.71/2.00  --inst_eq_res_simp                      false
% 11.71/2.00  --inst_subs_given                       false
% 11.71/2.00  --inst_orphan_elimination               true
% 11.71/2.00  --inst_learning_loop_flag               true
% 11.71/2.00  --inst_learning_start                   3000
% 11.71/2.00  --inst_learning_factor                  2
% 11.71/2.00  --inst_start_prop_sim_after_learn       3
% 11.71/2.00  --inst_sel_renew                        solver
% 11.71/2.00  --inst_lit_activity_flag                true
% 11.71/2.00  --inst_restr_to_given                   false
% 11.71/2.00  --inst_activity_threshold               500
% 11.71/2.00  --inst_out_proof                        true
% 11.71/2.00  
% 11.71/2.00  ------ Resolution Options
% 11.71/2.00  
% 11.71/2.00  --resolution_flag                       true
% 11.71/2.00  --res_lit_sel                           adaptive
% 11.71/2.00  --res_lit_sel_side                      none
% 11.71/2.00  --res_ordering                          kbo
% 11.71/2.00  --res_to_prop_solver                    active
% 11.71/2.00  --res_prop_simpl_new                    false
% 11.71/2.00  --res_prop_simpl_given                  true
% 11.71/2.00  --res_passive_queue_type                priority_queues
% 11.71/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.71/2.00  --res_passive_queues_freq               [15;5]
% 11.71/2.00  --res_forward_subs                      full
% 11.71/2.00  --res_backward_subs                     full
% 11.71/2.00  --res_forward_subs_resolution           true
% 11.71/2.00  --res_backward_subs_resolution          true
% 11.71/2.00  --res_orphan_elimination                true
% 11.71/2.00  --res_time_limit                        2.
% 11.71/2.00  --res_out_proof                         true
% 11.71/2.00  
% 11.71/2.00  ------ Superposition Options
% 11.71/2.00  
% 11.71/2.00  --superposition_flag                    true
% 11.71/2.00  --sup_passive_queue_type                priority_queues
% 11.71/2.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.71/2.00  --sup_passive_queues_freq               [1;4]
% 11.71/2.00  --demod_completeness_check              fast
% 11.71/2.00  --demod_use_ground                      true
% 11.71/2.00  --sup_to_prop_solver                    passive
% 11.71/2.00  --sup_prop_simpl_new                    true
% 11.71/2.00  --sup_prop_simpl_given                  true
% 11.71/2.00  --sup_fun_splitting                     false
% 11.71/2.00  --sup_smt_interval                      50000
% 11.71/2.00  
% 11.71/2.00  ------ Superposition Simplification Setup
% 11.71/2.00  
% 11.71/2.00  --sup_indices_passive                   []
% 11.71/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.71/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.71/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.71/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.71/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.71/2.00  --sup_full_bw                           [BwDemod]
% 11.71/2.00  --sup_immed_triv                        [TrivRules]
% 11.71/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.71/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.71/2.00  --sup_immed_bw_main                     []
% 11.71/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.71/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.71/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.71/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.71/2.00  
% 11.71/2.00  ------ Combination Options
% 11.71/2.00  
% 11.71/2.00  --comb_res_mult                         3
% 11.71/2.00  --comb_sup_mult                         2
% 11.71/2.00  --comb_inst_mult                        10
% 11.71/2.00  
% 11.71/2.00  ------ Debug Options
% 11.71/2.00  
% 11.71/2.00  --dbg_backtrace                         false
% 11.71/2.00  --dbg_dump_prop_clauses                 false
% 11.71/2.00  --dbg_dump_prop_clauses_file            -
% 11.71/2.00  --dbg_out_stat                          false
% 11.71/2.00  ------ Parsing...
% 11.71/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.71/2.00  
% 11.71/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.71/2.00  
% 11.71/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.71/2.00  
% 11.71/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.71/2.00  ------ Proving...
% 11.71/2.00  ------ Problem Properties 
% 11.71/2.00  
% 11.71/2.00  
% 11.71/2.00  clauses                                 12
% 11.71/2.00  conjectures                             3
% 11.71/2.00  EPR                                     5
% 11.71/2.00  Horn                                    12
% 11.71/2.00  unary                                   7
% 11.71/2.00  binary                                  3
% 11.71/2.00  lits                                    19
% 11.71/2.00  lits eq                                 4
% 11.71/2.00  fd_pure                                 0
% 11.71/2.00  fd_pseudo                               0
% 11.71/2.00  fd_cond                                 0
% 11.71/2.00  fd_pseudo_cond                          1
% 11.71/2.00  AC symbols                              0
% 11.71/2.00  
% 11.71/2.00  ------ Input Options Time Limit: Unbounded
% 11.71/2.00  
% 11.71/2.00  
% 11.71/2.00  ------ 
% 11.71/2.00  Current options:
% 11.71/2.00  ------ 
% 11.71/2.00  
% 11.71/2.00  ------ Input Options
% 11.71/2.00  
% 11.71/2.00  --out_options                           all
% 11.71/2.00  --tptp_safe_out                         true
% 11.71/2.00  --problem_path                          ""
% 11.71/2.00  --include_path                          ""
% 11.71/2.00  --clausifier                            res/vclausify_rel
% 11.71/2.00  --clausifier_options                    --mode clausify
% 11.71/2.00  --stdin                                 false
% 11.71/2.00  --stats_out                             sel
% 11.71/2.00  
% 11.71/2.00  ------ General Options
% 11.71/2.00  
% 11.71/2.00  --fof                                   false
% 11.71/2.00  --time_out_real                         604.99
% 11.71/2.00  --time_out_virtual                      -1.
% 11.71/2.00  --symbol_type_check                     false
% 11.71/2.00  --clausify_out                          false
% 11.71/2.00  --sig_cnt_out                           false
% 11.71/2.00  --trig_cnt_out                          false
% 11.71/2.00  --trig_cnt_out_tolerance                1.
% 11.71/2.00  --trig_cnt_out_sk_spl                   false
% 11.71/2.00  --abstr_cl_out                          false
% 11.71/2.00  
% 11.71/2.00  ------ Global Options
% 11.71/2.00  
% 11.71/2.00  --schedule                              none
% 11.71/2.00  --add_important_lit                     false
% 11.71/2.00  --prop_solver_per_cl                    1000
% 11.71/2.00  --min_unsat_core                        false
% 11.71/2.00  --soft_assumptions                      false
% 11.71/2.00  --soft_lemma_size                       3
% 11.71/2.00  --prop_impl_unit_size                   0
% 11.71/2.00  --prop_impl_unit                        []
% 11.71/2.00  --share_sel_clauses                     true
% 11.71/2.00  --reset_solvers                         false
% 11.71/2.00  --bc_imp_inh                            [conj_cone]
% 11.71/2.00  --conj_cone_tolerance                   3.
% 11.71/2.00  --extra_neg_conj                        none
% 11.71/2.00  --large_theory_mode                     true
% 11.71/2.00  --prolific_symb_bound                   200
% 11.71/2.00  --lt_threshold                          2000
% 11.71/2.00  --clause_weak_htbl                      true
% 11.71/2.00  --gc_record_bc_elim                     false
% 11.71/2.00  
% 11.71/2.00  ------ Preprocessing Options
% 11.71/2.00  
% 11.71/2.00  --preprocessing_flag                    true
% 11.71/2.00  --time_out_prep_mult                    0.1
% 11.71/2.00  --splitting_mode                        input
% 11.71/2.00  --splitting_grd                         true
% 11.71/2.00  --splitting_cvd                         false
% 11.71/2.00  --splitting_cvd_svl                     false
% 11.71/2.00  --splitting_nvd                         32
% 11.71/2.00  --sub_typing                            true
% 11.71/2.00  --prep_gs_sim                           false
% 11.71/2.00  --prep_unflatten                        true
% 11.71/2.00  --prep_res_sim                          true
% 11.71/2.00  --prep_upred                            true
% 11.71/2.00  --prep_sem_filter                       exhaustive
% 11.71/2.00  --prep_sem_filter_out                   false
% 11.71/2.00  --pred_elim                             false
% 11.71/2.00  --res_sim_input                         true
% 11.71/2.00  --eq_ax_congr_red                       true
% 11.71/2.00  --pure_diseq_elim                       true
% 11.71/2.00  --brand_transform                       false
% 11.71/2.00  --non_eq_to_eq                          false
% 11.71/2.00  --prep_def_merge                        true
% 11.71/2.00  --prep_def_merge_prop_impl              false
% 11.71/2.00  --prep_def_merge_mbd                    true
% 11.71/2.00  --prep_def_merge_tr_red                 false
% 11.71/2.00  --prep_def_merge_tr_cl                  false
% 11.71/2.00  --smt_preprocessing                     true
% 11.71/2.00  --smt_ac_axioms                         fast
% 11.71/2.00  --preprocessed_out                      false
% 11.71/2.00  --preprocessed_stats                    false
% 11.71/2.00  
% 11.71/2.00  ------ Abstraction refinement Options
% 11.71/2.00  
% 11.71/2.00  --abstr_ref                             []
% 11.71/2.00  --abstr_ref_prep                        false
% 11.71/2.00  --abstr_ref_until_sat                   false
% 11.71/2.00  --abstr_ref_sig_restrict                funpre
% 11.71/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.71/2.00  --abstr_ref_under                       []
% 11.71/2.00  
% 11.71/2.00  ------ SAT Options
% 11.71/2.00  
% 11.71/2.00  --sat_mode                              false
% 11.71/2.00  --sat_fm_restart_options                ""
% 11.71/2.00  --sat_gr_def                            false
% 11.71/2.00  --sat_epr_types                         true
% 11.71/2.00  --sat_non_cyclic_types                  false
% 11.71/2.00  --sat_finite_models                     false
% 11.71/2.00  --sat_fm_lemmas                         false
% 11.71/2.00  --sat_fm_prep                           false
% 11.71/2.00  --sat_fm_uc_incr                        true
% 11.71/2.00  --sat_out_model                         small
% 11.71/2.00  --sat_out_clauses                       false
% 11.71/2.00  
% 11.71/2.00  ------ QBF Options
% 11.71/2.00  
% 11.71/2.00  --qbf_mode                              false
% 11.71/2.00  --qbf_elim_univ                         false
% 11.71/2.00  --qbf_dom_inst                          none
% 11.71/2.00  --qbf_dom_pre_inst                      false
% 11.71/2.00  --qbf_sk_in                             false
% 11.71/2.00  --qbf_pred_elim                         true
% 11.71/2.00  --qbf_split                             512
% 11.71/2.00  
% 11.71/2.00  ------ BMC1 Options
% 11.71/2.00  
% 11.71/2.00  --bmc1_incremental                      false
% 11.71/2.00  --bmc1_axioms                           reachable_all
% 11.71/2.00  --bmc1_min_bound                        0
% 11.71/2.00  --bmc1_max_bound                        -1
% 11.71/2.00  --bmc1_max_bound_default                -1
% 11.71/2.00  --bmc1_symbol_reachability              true
% 11.71/2.00  --bmc1_property_lemmas                  false
% 11.71/2.00  --bmc1_k_induction                      false
% 11.71/2.00  --bmc1_non_equiv_states                 false
% 11.71/2.00  --bmc1_deadlock                         false
% 11.71/2.00  --bmc1_ucm                              false
% 11.71/2.00  --bmc1_add_unsat_core                   none
% 11.71/2.00  --bmc1_unsat_core_children              false
% 11.71/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.71/2.00  --bmc1_out_stat                         full
% 11.71/2.00  --bmc1_ground_init                      false
% 11.71/2.00  --bmc1_pre_inst_next_state              false
% 11.71/2.00  --bmc1_pre_inst_state                   false
% 11.71/2.00  --bmc1_pre_inst_reach_state             false
% 11.71/2.00  --bmc1_out_unsat_core                   false
% 11.71/2.00  --bmc1_aig_witness_out                  false
% 11.71/2.00  --bmc1_verbose                          false
% 11.71/2.00  --bmc1_dump_clauses_tptp                false
% 11.71/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.71/2.00  --bmc1_dump_file                        -
% 11.71/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.71/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.71/2.00  --bmc1_ucm_extend_mode                  1
% 11.71/2.00  --bmc1_ucm_init_mode                    2
% 11.71/2.00  --bmc1_ucm_cone_mode                    none
% 11.71/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.71/2.00  --bmc1_ucm_relax_model                  4
% 11.71/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.71/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.71/2.00  --bmc1_ucm_layered_model                none
% 11.71/2.00  --bmc1_ucm_max_lemma_size               10
% 11.71/2.00  
% 11.71/2.00  ------ AIG Options
% 11.71/2.00  
% 11.71/2.00  --aig_mode                              false
% 11.71/2.00  
% 11.71/2.00  ------ Instantiation Options
% 11.71/2.00  
% 11.71/2.00  --instantiation_flag                    true
% 11.71/2.00  --inst_sos_flag                         false
% 11.71/2.00  --inst_sos_phase                        true
% 11.71/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.71/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.71/2.00  --inst_lit_sel_side                     num_symb
% 11.71/2.00  --inst_solver_per_active                1400
% 11.71/2.00  --inst_solver_calls_frac                1.
% 11.71/2.00  --inst_passive_queue_type               priority_queues
% 11.71/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.71/2.00  --inst_passive_queues_freq              [25;2]
% 11.71/2.00  --inst_dismatching                      true
% 11.71/2.00  --inst_eager_unprocessed_to_passive     true
% 11.71/2.00  --inst_prop_sim_given                   true
% 11.71/2.00  --inst_prop_sim_new                     false
% 11.71/2.00  --inst_subs_new                         false
% 11.71/2.00  --inst_eq_res_simp                      false
% 11.71/2.00  --inst_subs_given                       false
% 11.71/2.00  --inst_orphan_elimination               true
% 11.71/2.00  --inst_learning_loop_flag               true
% 11.71/2.00  --inst_learning_start                   3000
% 11.71/2.00  --inst_learning_factor                  2
% 11.71/2.00  --inst_start_prop_sim_after_learn       3
% 11.71/2.00  --inst_sel_renew                        solver
% 11.71/2.00  --inst_lit_activity_flag                true
% 11.71/2.00  --inst_restr_to_given                   false
% 11.71/2.00  --inst_activity_threshold               500
% 11.71/2.00  --inst_out_proof                        true
% 11.71/2.00  
% 11.71/2.00  ------ Resolution Options
% 11.71/2.00  
% 11.71/2.00  --resolution_flag                       true
% 11.71/2.00  --res_lit_sel                           adaptive
% 11.71/2.00  --res_lit_sel_side                      none
% 11.71/2.00  --res_ordering                          kbo
% 11.71/2.00  --res_to_prop_solver                    active
% 11.71/2.00  --res_prop_simpl_new                    false
% 11.71/2.00  --res_prop_simpl_given                  true
% 11.71/2.00  --res_passive_queue_type                priority_queues
% 11.71/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.71/2.00  --res_passive_queues_freq               [15;5]
% 11.71/2.00  --res_forward_subs                      full
% 11.71/2.00  --res_backward_subs                     full
% 11.71/2.00  --res_forward_subs_resolution           true
% 11.71/2.00  --res_backward_subs_resolution          true
% 11.71/2.00  --res_orphan_elimination                true
% 11.71/2.00  --res_time_limit                        2.
% 11.71/2.00  --res_out_proof                         true
% 11.71/2.00  
% 11.71/2.00  ------ Superposition Options
% 11.71/2.00  
% 11.71/2.00  --superposition_flag                    true
% 11.71/2.00  --sup_passive_queue_type                priority_queues
% 11.71/2.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.71/2.00  --sup_passive_queues_freq               [1;4]
% 11.71/2.00  --demod_completeness_check              fast
% 11.71/2.00  --demod_use_ground                      true
% 11.71/2.00  --sup_to_prop_solver                    passive
% 11.71/2.00  --sup_prop_simpl_new                    true
% 11.71/2.00  --sup_prop_simpl_given                  true
% 11.71/2.00  --sup_fun_splitting                     false
% 11.71/2.00  --sup_smt_interval                      50000
% 11.71/2.00  
% 11.71/2.00  ------ Superposition Simplification Setup
% 11.71/2.00  
% 11.71/2.00  --sup_indices_passive                   []
% 11.71/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.71/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.71/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.71/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.71/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.71/2.00  --sup_full_bw                           [BwDemod]
% 11.71/2.00  --sup_immed_triv                        [TrivRules]
% 11.71/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.71/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.71/2.00  --sup_immed_bw_main                     []
% 11.71/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.71/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.71/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.71/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.71/2.00  
% 11.71/2.00  ------ Combination Options
% 11.71/2.00  
% 11.71/2.00  --comb_res_mult                         3
% 11.71/2.00  --comb_sup_mult                         2
% 11.71/2.00  --comb_inst_mult                        10
% 11.71/2.00  
% 11.71/2.00  ------ Debug Options
% 11.71/2.00  
% 11.71/2.00  --dbg_backtrace                         false
% 11.71/2.00  --dbg_dump_prop_clauses                 false
% 11.71/2.00  --dbg_dump_prop_clauses_file            -
% 11.71/2.00  --dbg_out_stat                          false
% 11.71/2.00  
% 11.71/2.00  
% 11.71/2.00  
% 11.71/2.00  
% 11.71/2.00  ------ Proving...
% 11.71/2.00  
% 11.71/2.00  
% 11.71/2.00  % SZS status Theorem for theBenchmark.p
% 11.71/2.00  
% 11.71/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.71/2.00  
% 11.71/2.00  fof(f10,conjecture,(
% 11.71/2.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 11.71/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.71/2.00  
% 11.71/2.00  fof(f11,negated_conjecture,(
% 11.71/2.00    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 11.71/2.00    inference(negated_conjecture,[],[f10])).
% 11.71/2.00  
% 11.71/2.00  fof(f18,plain,(
% 11.71/2.00    ? [X0,X1,X2] : ((~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 11.71/2.00    inference(ennf_transformation,[],[f11])).
% 11.71/2.00  
% 11.71/2.00  fof(f19,plain,(
% 11.71/2.00    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 11.71/2.00    inference(flattening,[],[f18])).
% 11.71/2.00  
% 11.71/2.00  fof(f22,plain,(
% 11.71/2.00    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 11.71/2.00    introduced(choice_axiom,[])).
% 11.71/2.00  
% 11.71/2.00  fof(f23,plain,(
% 11.71/2.00    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 11.71/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f22])).
% 11.71/2.00  
% 11.71/2.00  fof(f36,plain,(
% 11.71/2.00    r1_tarski(sK0,sK1)),
% 11.71/2.00    inference(cnf_transformation,[],[f23])).
% 11.71/2.00  
% 11.71/2.00  fof(f2,axiom,(
% 11.71/2.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.71/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.71/2.00  
% 11.71/2.00  fof(f20,plain,(
% 11.71/2.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.71/2.00    inference(nnf_transformation,[],[f2])).
% 11.71/2.00  
% 11.71/2.00  fof(f21,plain,(
% 11.71/2.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.71/2.00    inference(flattening,[],[f20])).
% 11.71/2.00  
% 11.71/2.00  fof(f25,plain,(
% 11.71/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.71/2.00    inference(cnf_transformation,[],[f21])).
% 11.71/2.00  
% 11.71/2.00  fof(f44,plain,(
% 11.71/2.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.71/2.00    inference(equality_resolution,[],[f25])).
% 11.71/2.00  
% 11.71/2.00  fof(f4,axiom,(
% 11.71/2.00    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 11.71/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.71/2.00  
% 11.71/2.00  fof(f15,plain,(
% 11.71/2.00    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 11.71/2.00    inference(ennf_transformation,[],[f4])).
% 11.71/2.00  
% 11.71/2.00  fof(f29,plain,(
% 11.71/2.00    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 11.71/2.00    inference(cnf_transformation,[],[f15])).
% 11.71/2.00  
% 11.71/2.00  fof(f8,axiom,(
% 11.71/2.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 11.71/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.71/2.00  
% 11.71/2.00  fof(f33,plain,(
% 11.71/2.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 11.71/2.00    inference(cnf_transformation,[],[f8])).
% 11.71/2.00  
% 11.71/2.00  fof(f39,plain,(
% 11.71/2.00    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))) )),
% 11.71/2.00    inference(definition_unfolding,[],[f29,f33])).
% 11.71/2.00  
% 11.71/2.00  fof(f3,axiom,(
% 11.71/2.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 11.71/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.71/2.00  
% 11.71/2.00  fof(f13,plain,(
% 11.71/2.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 11.71/2.00    inference(ennf_transformation,[],[f3])).
% 11.71/2.00  
% 11.71/2.00  fof(f14,plain,(
% 11.71/2.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 11.71/2.00    inference(flattening,[],[f13])).
% 11.71/2.00  
% 11.71/2.00  fof(f28,plain,(
% 11.71/2.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 11.71/2.00    inference(cnf_transformation,[],[f14])).
% 11.71/2.00  
% 11.71/2.00  fof(f1,axiom,(
% 11.71/2.00    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 11.71/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.71/2.00  
% 11.71/2.00  fof(f12,plain,(
% 11.71/2.00    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 11.71/2.00    inference(rectify,[],[f1])).
% 11.71/2.00  
% 11.71/2.00  fof(f24,plain,(
% 11.71/2.00    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 11.71/2.00    inference(cnf_transformation,[],[f12])).
% 11.71/2.00  
% 11.71/2.00  fof(f38,plain,(
% 11.71/2.00    ( ! [X0] : (k3_tarski(k2_tarski(X0,X0)) = X0) )),
% 11.71/2.00    inference(definition_unfolding,[],[f24,f33])).
% 11.71/2.00  
% 11.71/2.00  fof(f5,axiom,(
% 11.71/2.00    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 11.71/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.71/2.00  
% 11.71/2.00  fof(f16,plain,(
% 11.71/2.00    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 11.71/2.00    inference(ennf_transformation,[],[f5])).
% 11.71/2.00  
% 11.71/2.00  fof(f30,plain,(
% 11.71/2.00    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 11.71/2.00    inference(cnf_transformation,[],[f16])).
% 11.71/2.00  
% 11.71/2.00  fof(f40,plain,(
% 11.71/2.00    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 11.71/2.00    inference(definition_unfolding,[],[f30,f33])).
% 11.71/2.00  
% 11.71/2.00  fof(f7,axiom,(
% 11.71/2.00    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 11.71/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.71/2.00  
% 11.71/2.00  fof(f32,plain,(
% 11.71/2.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 11.71/2.00    inference(cnf_transformation,[],[f7])).
% 11.71/2.00  
% 11.71/2.00  fof(f6,axiom,(
% 11.71/2.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 11.71/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.71/2.00  
% 11.71/2.00  fof(f31,plain,(
% 11.71/2.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 11.71/2.00    inference(cnf_transformation,[],[f6])).
% 11.71/2.00  
% 11.71/2.00  fof(f41,plain,(
% 11.71/2.00    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 11.71/2.00    inference(definition_unfolding,[],[f31,f33])).
% 11.71/2.00  
% 11.71/2.00  fof(f27,plain,(
% 11.71/2.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.71/2.00    inference(cnf_transformation,[],[f21])).
% 11.71/2.00  
% 11.71/2.00  fof(f35,plain,(
% 11.71/2.00    v1_relat_1(sK2)),
% 11.71/2.00    inference(cnf_transformation,[],[f23])).
% 11.71/2.00  
% 11.71/2.00  fof(f9,axiom,(
% 11.71/2.00    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)))),
% 11.71/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.71/2.00  
% 11.71/2.00  fof(f17,plain,(
% 11.71/2.00    ! [X0,X1,X2] : (k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 11.71/2.00    inference(ennf_transformation,[],[f9])).
% 11.71/2.00  
% 11.71/2.00  fof(f34,plain,(
% 11.71/2.00    ( ! [X2,X0,X1] : (k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 11.71/2.00    inference(cnf_transformation,[],[f17])).
% 11.71/2.00  
% 11.71/2.00  fof(f42,plain,(
% 11.71/2.00    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) = k10_relat_1(X2,k3_tarski(k2_tarski(X0,X1))) | ~v1_relat_1(X2)) )),
% 11.71/2.00    inference(definition_unfolding,[],[f34,f33,f33])).
% 11.71/2.00  
% 11.71/2.00  fof(f37,plain,(
% 11.71/2.00    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 11.71/2.00    inference(cnf_transformation,[],[f23])).
% 11.71/2.00  
% 11.71/2.00  cnf(c_11,negated_conjecture,
% 11.71/2.00      ( r1_tarski(sK0,sK1) ),
% 11.71/2.00      inference(cnf_transformation,[],[f36]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_448,plain,
% 11.71/2.00      ( r1_tarski(sK0,sK1) = iProver_top ),
% 11.71/2.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_3,plain,
% 11.71/2.00      ( r1_tarski(X0,X0) ),
% 11.71/2.00      inference(cnf_transformation,[],[f44]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_455,plain,
% 11.71/2.00      ( r1_tarski(X0,X0) = iProver_top ),
% 11.71/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_5,plain,
% 11.71/2.00      ( ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
% 11.71/2.00      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 11.71/2.00      inference(cnf_transformation,[],[f39]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_453,plain,
% 11.71/2.00      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) != iProver_top
% 11.71/2.00      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 11.71/2.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_1145,plain,
% 11.71/2.00      ( r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1) = iProver_top ),
% 11.71/2.00      inference(superposition,[status(thm)],[c_455,c_453]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_4,plain,
% 11.71/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 11.71/2.00      inference(cnf_transformation,[],[f28]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_454,plain,
% 11.71/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.71/2.00      | r1_tarski(X1,X2) != iProver_top
% 11.71/2.00      | r1_tarski(X0,X2) = iProver_top ),
% 11.71/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_2486,plain,
% 11.71/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.71/2.00      | r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X2,X0)),X2),X1) = iProver_top ),
% 11.71/2.00      inference(superposition,[status(thm)],[c_1145,c_454]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_0,plain,
% 11.71/2.00      ( k3_tarski(k2_tarski(X0,X0)) = X0 ),
% 11.71/2.00      inference(cnf_transformation,[],[f38]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_6,plain,
% 11.71/2.00      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
% 11.71/2.00      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 11.71/2.00      inference(cnf_transformation,[],[f40]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_452,plain,
% 11.71/2.00      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) = iProver_top
% 11.71/2.00      | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
% 11.71/2.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_990,plain,
% 11.71/2.00      ( r1_tarski(X0,X1) = iProver_top
% 11.71/2.00      | r1_tarski(k4_xboole_0(X0,X1),X1) != iProver_top ),
% 11.71/2.00      inference(superposition,[status(thm)],[c_0,c_452]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_24854,plain,
% 11.71/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.71/2.00      | r1_tarski(k3_tarski(k2_tarski(X1,X0)),X1) = iProver_top ),
% 11.71/2.00      inference(superposition,[status(thm)],[c_2486,c_990]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_8,plain,
% 11.71/2.00      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 11.71/2.00      inference(cnf_transformation,[],[f32]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_7,plain,
% 11.71/2.00      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
% 11.71/2.00      inference(cnf_transformation,[],[f41]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_451,plain,
% 11.71/2.00      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
% 11.71/2.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_869,plain,
% 11.71/2.00      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
% 11.71/2.00      inference(superposition,[status(thm)],[c_8,c_451]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_1,plain,
% 11.71/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.71/2.00      inference(cnf_transformation,[],[f27]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_456,plain,
% 11.71/2.00      ( X0 = X1
% 11.71/2.00      | r1_tarski(X0,X1) != iProver_top
% 11.71/2.00      | r1_tarski(X1,X0) != iProver_top ),
% 11.71/2.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_1351,plain,
% 11.71/2.00      ( k3_tarski(k2_tarski(X0,X1)) = X1
% 11.71/2.00      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),X1) != iProver_top ),
% 11.71/2.00      inference(superposition,[status(thm)],[c_869,c_456]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_5647,plain,
% 11.71/2.00      ( k3_tarski(k2_tarski(X0,X1)) = X1
% 11.71/2.00      | r1_tarski(k3_tarski(k2_tarski(X1,X0)),X1) != iProver_top ),
% 11.71/2.00      inference(superposition,[status(thm)],[c_8,c_1351]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_44290,plain,
% 11.71/2.00      ( k3_tarski(k2_tarski(X0,X1)) = X1
% 11.71/2.00      | r1_tarski(X0,X1) != iProver_top ),
% 11.71/2.00      inference(superposition,[status(thm)],[c_24854,c_5647]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_45463,plain,
% 11.71/2.00      ( k3_tarski(k2_tarski(sK0,sK1)) = sK1 ),
% 11.71/2.00      inference(superposition,[status(thm)],[c_448,c_44290]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_12,negated_conjecture,
% 11.71/2.00      ( v1_relat_1(sK2) ),
% 11.71/2.00      inference(cnf_transformation,[],[f35]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_447,plain,
% 11.71/2.00      ( v1_relat_1(sK2) = iProver_top ),
% 11.71/2.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_9,plain,
% 11.71/2.00      ( ~ v1_relat_1(X0)
% 11.71/2.00      | k3_tarski(k2_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,X2))) = k10_relat_1(X0,k3_tarski(k2_tarski(X1,X2))) ),
% 11.71/2.00      inference(cnf_transformation,[],[f42]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_450,plain,
% 11.71/2.00      ( k3_tarski(k2_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,X2))) = k10_relat_1(X0,k3_tarski(k2_tarski(X1,X2)))
% 11.71/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.71/2.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_1140,plain,
% 11.71/2.00      ( k3_tarski(k2_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) = k10_relat_1(sK2,k3_tarski(k2_tarski(X0,X1))) ),
% 11.71/2.00      inference(superposition,[status(thm)],[c_447,c_450]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_2763,plain,
% 11.71/2.00      ( r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,k3_tarski(k2_tarski(X0,X1)))) = iProver_top ),
% 11.71/2.00      inference(superposition,[status(thm)],[c_1140,c_451]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_45936,plain,
% 11.71/2.00      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
% 11.71/2.00      inference(superposition,[status(thm)],[c_45463,c_2763]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_10,negated_conjecture,
% 11.71/2.00      ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
% 11.71/2.00      inference(cnf_transformation,[],[f37]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(c_15,plain,
% 11.71/2.00      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) != iProver_top ),
% 11.71/2.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.71/2.00  
% 11.71/2.00  cnf(contradiction,plain,
% 11.71/2.00      ( $false ),
% 11.71/2.00      inference(minisat,[status(thm)],[c_45936,c_15]) ).
% 11.71/2.00  
% 11.71/2.00  
% 11.71/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.71/2.00  
% 11.71/2.00  ------                               Statistics
% 11.71/2.00  
% 11.71/2.00  ------ Selected
% 11.71/2.00  
% 11.71/2.00  total_time:                             1.356
% 11.71/2.00  
%------------------------------------------------------------------------------
