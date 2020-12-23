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
% DateTime   : Thu Dec  3 11:25:10 EST 2020

% Result     : Theorem 51.70s
% Output     : CNFRefutation 51.70s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 149 expanded)
%              Number of clauses        :   42 (  66 expanded)
%              Number of leaves         :   11 (  32 expanded)
%              Depth                    :   17
%              Number of atoms          :  106 ( 233 expanded)
%              Number of equality atoms :   57 ( 113 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f20])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k4_xboole_0(X1,X0),X2)
        & r1_tarski(k4_xboole_0(X0,X1),X2) )
     => r1_tarski(k5_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(k4_xboole_0(X1,X0),X2)
          & r1_tarski(k4_xboole_0(X0,X1),X2) )
       => r1_tarski(k5_xboole_0(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X1),X2)
      & r1_tarski(k4_xboole_0(X1,X0),X2)
      & r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X1),X2)
      & r1_tarski(k4_xboole_0(X1,X0),X2)
      & r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(flattening,[],[f15])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_xboole_0(X0,X1),X2)
        & r1_tarski(k4_xboole_0(X1,X0),X2)
        & r1_tarski(k4_xboole_0(X0,X1),X2) )
   => ( ~ r1_tarski(k5_xboole_0(sK0,sK1),sK2)
      & r1_tarski(k4_xboole_0(sK1,sK0),sK2)
      & r1_tarski(k4_xboole_0(sK0,sK1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK1),sK2)
    & r1_tarski(k4_xboole_0(sK1,sK0),sK2)
    & r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).

fof(f32,plain,(
    r1_tarski(k4_xboole_0(sK1,sK0),sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f31,plain,(
    r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f33,plain,(
    ~ r1_tarski(k5_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    ~ r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2) ),
    inference(definition_unfolding,[],[f33,f20])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_5,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_353,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_512,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_353])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_357,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1890,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_512,c_357])).

cnf(c_2,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_8,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(k4_xboole_0(sK1,sK0),sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_350,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK0),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_355,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_941,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK0),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_350,c_355])).

cnf(c_695,plain,
    ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_353])).

cnf(c_949,plain,
    ( r1_tarski(k4_xboole_0(X0,sK2),k4_xboole_0(X0,k4_xboole_0(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_941,c_695])).

cnf(c_1022,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,X1),sK2),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(sK1,sK0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_949])).

cnf(c_1024,plain,
    ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,sK2)),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(sK1,sK0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1022,c_8])).

cnf(c_15010,plain,
    ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)),k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1024])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_349,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_942,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_349,c_355])).

cnf(c_15038,plain,
    ( r1_tarski(k4_xboole_0(X0,sK2),k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15010,c_942])).

cnf(c_9,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_352,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_15292,plain,
    ( r1_tarski(X0,k2_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_15038,c_352])).

cnf(c_154092,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(sK2,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1890,c_15292])).

cnf(c_1887,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_353,c_357])).

cnf(c_6,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_143291,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1887,c_6])).

cnf(c_940,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_353,c_355])).

cnf(c_697,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_8,c_6])).

cnf(c_20398,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_940,c_697])).

cnf(c_20430,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_20398,c_6])).

cnf(c_146431,plain,
    ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_143291,c_20430])).

cnf(c_943,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_512,c_355])).

cnf(c_146503,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_146431,c_943])).

cnf(c_154309,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_154092,c_146503])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_351,plain,
    ( r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_475,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_351,c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_154309,c_475])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:20:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 51.70/7.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.70/7.00  
% 51.70/7.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.70/7.00  
% 51.70/7.00  ------  iProver source info
% 51.70/7.00  
% 51.70/7.00  git: date: 2020-06-30 10:37:57 +0100
% 51.70/7.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.70/7.00  git: non_committed_changes: false
% 51.70/7.00  git: last_make_outside_of_git: false
% 51.70/7.00  
% 51.70/7.00  ------ 
% 51.70/7.00  
% 51.70/7.00  ------ Input Options
% 51.70/7.00  
% 51.70/7.00  --out_options                           all
% 51.70/7.00  --tptp_safe_out                         true
% 51.70/7.00  --problem_path                          ""
% 51.70/7.00  --include_path                          ""
% 51.70/7.00  --clausifier                            res/vclausify_rel
% 51.70/7.00  --clausifier_options                    ""
% 51.70/7.00  --stdin                                 false
% 51.70/7.00  --stats_out                             all
% 51.70/7.00  
% 51.70/7.00  ------ General Options
% 51.70/7.00  
% 51.70/7.00  --fof                                   false
% 51.70/7.00  --time_out_real                         305.
% 51.70/7.00  --time_out_virtual                      -1.
% 51.70/7.00  --symbol_type_check                     false
% 51.70/7.00  --clausify_out                          false
% 51.70/7.00  --sig_cnt_out                           false
% 51.70/7.00  --trig_cnt_out                          false
% 51.70/7.00  --trig_cnt_out_tolerance                1.
% 51.70/7.00  --trig_cnt_out_sk_spl                   false
% 51.70/7.00  --abstr_cl_out                          false
% 51.70/7.00  
% 51.70/7.00  ------ Global Options
% 51.70/7.00  
% 51.70/7.00  --schedule                              default
% 51.70/7.00  --add_important_lit                     false
% 51.70/7.00  --prop_solver_per_cl                    1000
% 51.70/7.00  --min_unsat_core                        false
% 51.70/7.00  --soft_assumptions                      false
% 51.70/7.00  --soft_lemma_size                       3
% 51.70/7.00  --prop_impl_unit_size                   0
% 51.70/7.00  --prop_impl_unit                        []
% 51.70/7.00  --share_sel_clauses                     true
% 51.70/7.00  --reset_solvers                         false
% 51.70/7.00  --bc_imp_inh                            [conj_cone]
% 51.70/7.00  --conj_cone_tolerance                   3.
% 51.70/7.00  --extra_neg_conj                        none
% 51.70/7.00  --large_theory_mode                     true
% 51.70/7.00  --prolific_symb_bound                   200
% 51.70/7.00  --lt_threshold                          2000
% 51.70/7.00  --clause_weak_htbl                      true
% 51.70/7.00  --gc_record_bc_elim                     false
% 51.70/7.00  
% 51.70/7.00  ------ Preprocessing Options
% 51.70/7.00  
% 51.70/7.00  --preprocessing_flag                    true
% 51.70/7.00  --time_out_prep_mult                    0.1
% 51.70/7.00  --splitting_mode                        input
% 51.70/7.00  --splitting_grd                         true
% 51.70/7.00  --splitting_cvd                         false
% 51.70/7.00  --splitting_cvd_svl                     false
% 51.70/7.00  --splitting_nvd                         32
% 51.70/7.00  --sub_typing                            true
% 51.70/7.00  --prep_gs_sim                           true
% 51.70/7.00  --prep_unflatten                        true
% 51.70/7.00  --prep_res_sim                          true
% 51.70/7.00  --prep_upred                            true
% 51.70/7.00  --prep_sem_filter                       exhaustive
% 51.70/7.00  --prep_sem_filter_out                   false
% 51.70/7.00  --pred_elim                             true
% 51.70/7.00  --res_sim_input                         true
% 51.70/7.00  --eq_ax_congr_red                       true
% 51.70/7.00  --pure_diseq_elim                       true
% 51.70/7.00  --brand_transform                       false
% 51.70/7.00  --non_eq_to_eq                          false
% 51.70/7.00  --prep_def_merge                        true
% 51.70/7.00  --prep_def_merge_prop_impl              false
% 51.70/7.00  --prep_def_merge_mbd                    true
% 51.70/7.00  --prep_def_merge_tr_red                 false
% 51.70/7.00  --prep_def_merge_tr_cl                  false
% 51.70/7.00  --smt_preprocessing                     true
% 51.70/7.00  --smt_ac_axioms                         fast
% 51.70/7.00  --preprocessed_out                      false
% 51.70/7.00  --preprocessed_stats                    false
% 51.70/7.00  
% 51.70/7.00  ------ Abstraction refinement Options
% 51.70/7.00  
% 51.70/7.00  --abstr_ref                             []
% 51.70/7.00  --abstr_ref_prep                        false
% 51.70/7.00  --abstr_ref_until_sat                   false
% 51.70/7.00  --abstr_ref_sig_restrict                funpre
% 51.70/7.00  --abstr_ref_af_restrict_to_split_sk     false
% 51.70/7.00  --abstr_ref_under                       []
% 51.70/7.00  
% 51.70/7.00  ------ SAT Options
% 51.70/7.00  
% 51.70/7.00  --sat_mode                              false
% 51.70/7.00  --sat_fm_restart_options                ""
% 51.70/7.00  --sat_gr_def                            false
% 51.70/7.00  --sat_epr_types                         true
% 51.70/7.00  --sat_non_cyclic_types                  false
% 51.70/7.00  --sat_finite_models                     false
% 51.70/7.00  --sat_fm_lemmas                         false
% 51.70/7.00  --sat_fm_prep                           false
% 51.70/7.00  --sat_fm_uc_incr                        true
% 51.70/7.00  --sat_out_model                         small
% 51.70/7.00  --sat_out_clauses                       false
% 51.70/7.00  
% 51.70/7.00  ------ QBF Options
% 51.70/7.00  
% 51.70/7.00  --qbf_mode                              false
% 51.70/7.00  --qbf_elim_univ                         false
% 51.70/7.00  --qbf_dom_inst                          none
% 51.70/7.00  --qbf_dom_pre_inst                      false
% 51.70/7.00  --qbf_sk_in                             false
% 51.70/7.00  --qbf_pred_elim                         true
% 51.70/7.00  --qbf_split                             512
% 51.70/7.00  
% 51.70/7.00  ------ BMC1 Options
% 51.70/7.00  
% 51.70/7.00  --bmc1_incremental                      false
% 51.70/7.00  --bmc1_axioms                           reachable_all
% 51.70/7.00  --bmc1_min_bound                        0
% 51.70/7.00  --bmc1_max_bound                        -1
% 51.70/7.00  --bmc1_max_bound_default                -1
% 51.70/7.00  --bmc1_symbol_reachability              true
% 51.70/7.00  --bmc1_property_lemmas                  false
% 51.70/7.00  --bmc1_k_induction                      false
% 51.70/7.00  --bmc1_non_equiv_states                 false
% 51.70/7.00  --bmc1_deadlock                         false
% 51.70/7.00  --bmc1_ucm                              false
% 51.70/7.00  --bmc1_add_unsat_core                   none
% 51.70/7.00  --bmc1_unsat_core_children              false
% 51.70/7.00  --bmc1_unsat_core_extrapolate_axioms    false
% 51.70/7.00  --bmc1_out_stat                         full
% 51.70/7.00  --bmc1_ground_init                      false
% 51.70/7.00  --bmc1_pre_inst_next_state              false
% 51.70/7.00  --bmc1_pre_inst_state                   false
% 51.70/7.00  --bmc1_pre_inst_reach_state             false
% 51.70/7.00  --bmc1_out_unsat_core                   false
% 51.70/7.00  --bmc1_aig_witness_out                  false
% 51.70/7.00  --bmc1_verbose                          false
% 51.70/7.00  --bmc1_dump_clauses_tptp                false
% 51.70/7.00  --bmc1_dump_unsat_core_tptp             false
% 51.70/7.00  --bmc1_dump_file                        -
% 51.70/7.00  --bmc1_ucm_expand_uc_limit              128
% 51.70/7.00  --bmc1_ucm_n_expand_iterations          6
% 51.70/7.00  --bmc1_ucm_extend_mode                  1
% 51.70/7.00  --bmc1_ucm_init_mode                    2
% 51.70/7.00  --bmc1_ucm_cone_mode                    none
% 51.70/7.00  --bmc1_ucm_reduced_relation_type        0
% 51.70/7.00  --bmc1_ucm_relax_model                  4
% 51.70/7.00  --bmc1_ucm_full_tr_after_sat            true
% 51.70/7.00  --bmc1_ucm_expand_neg_assumptions       false
% 51.70/7.00  --bmc1_ucm_layered_model                none
% 51.70/7.00  --bmc1_ucm_max_lemma_size               10
% 51.70/7.00  
% 51.70/7.00  ------ AIG Options
% 51.70/7.00  
% 51.70/7.00  --aig_mode                              false
% 51.70/7.00  
% 51.70/7.00  ------ Instantiation Options
% 51.70/7.00  
% 51.70/7.00  --instantiation_flag                    true
% 51.70/7.00  --inst_sos_flag                         true
% 51.70/7.00  --inst_sos_phase                        true
% 51.70/7.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.70/7.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.70/7.00  --inst_lit_sel_side                     num_symb
% 51.70/7.00  --inst_solver_per_active                1400
% 51.70/7.00  --inst_solver_calls_frac                1.
% 51.70/7.00  --inst_passive_queue_type               priority_queues
% 51.70/7.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.70/7.00  --inst_passive_queues_freq              [25;2]
% 51.70/7.00  --inst_dismatching                      true
% 51.70/7.00  --inst_eager_unprocessed_to_passive     true
% 51.70/7.00  --inst_prop_sim_given                   true
% 51.70/7.00  --inst_prop_sim_new                     false
% 51.70/7.00  --inst_subs_new                         false
% 51.70/7.00  --inst_eq_res_simp                      false
% 51.70/7.00  --inst_subs_given                       false
% 51.70/7.00  --inst_orphan_elimination               true
% 51.70/7.00  --inst_learning_loop_flag               true
% 51.70/7.00  --inst_learning_start                   3000
% 51.70/7.00  --inst_learning_factor                  2
% 51.70/7.00  --inst_start_prop_sim_after_learn       3
% 51.70/7.00  --inst_sel_renew                        solver
% 51.70/7.00  --inst_lit_activity_flag                true
% 51.70/7.00  --inst_restr_to_given                   false
% 51.70/7.00  --inst_activity_threshold               500
% 51.70/7.00  --inst_out_proof                        true
% 51.70/7.00  
% 51.70/7.00  ------ Resolution Options
% 51.70/7.00  
% 51.70/7.00  --resolution_flag                       true
% 51.70/7.00  --res_lit_sel                           adaptive
% 51.70/7.00  --res_lit_sel_side                      none
% 51.70/7.00  --res_ordering                          kbo
% 51.70/7.00  --res_to_prop_solver                    active
% 51.70/7.00  --res_prop_simpl_new                    false
% 51.70/7.00  --res_prop_simpl_given                  true
% 51.70/7.00  --res_passive_queue_type                priority_queues
% 51.70/7.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.70/7.00  --res_passive_queues_freq               [15;5]
% 51.70/7.00  --res_forward_subs                      full
% 51.70/7.00  --res_backward_subs                     full
% 51.70/7.00  --res_forward_subs_resolution           true
% 51.70/7.00  --res_backward_subs_resolution          true
% 51.70/7.00  --res_orphan_elimination                true
% 51.70/7.00  --res_time_limit                        2.
% 51.70/7.00  --res_out_proof                         true
% 51.70/7.00  
% 51.70/7.00  ------ Superposition Options
% 51.70/7.00  
% 51.70/7.00  --superposition_flag                    true
% 51.70/7.00  --sup_passive_queue_type                priority_queues
% 51.70/7.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.70/7.00  --sup_passive_queues_freq               [8;1;4]
% 51.70/7.00  --demod_completeness_check              fast
% 51.70/7.00  --demod_use_ground                      true
% 51.70/7.00  --sup_to_prop_solver                    passive
% 51.70/7.00  --sup_prop_simpl_new                    true
% 51.70/7.00  --sup_prop_simpl_given                  true
% 51.70/7.00  --sup_fun_splitting                     true
% 51.70/7.00  --sup_smt_interval                      50000
% 51.70/7.00  
% 51.70/7.00  ------ Superposition Simplification Setup
% 51.70/7.00  
% 51.70/7.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.70/7.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.70/7.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.70/7.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.70/7.00  --sup_full_triv                         [TrivRules;PropSubs]
% 51.70/7.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.70/7.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.70/7.00  --sup_immed_triv                        [TrivRules]
% 51.70/7.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.70/7.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.70/7.00  --sup_immed_bw_main                     []
% 51.70/7.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.70/7.00  --sup_input_triv                        [Unflattening;TrivRules]
% 51.70/7.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.70/7.00  --sup_input_bw                          []
% 51.70/7.00  
% 51.70/7.00  ------ Combination Options
% 51.70/7.00  
% 51.70/7.00  --comb_res_mult                         3
% 51.70/7.00  --comb_sup_mult                         2
% 51.70/7.00  --comb_inst_mult                        10
% 51.70/7.00  
% 51.70/7.00  ------ Debug Options
% 51.70/7.00  
% 51.70/7.00  --dbg_backtrace                         false
% 51.70/7.00  --dbg_dump_prop_clauses                 false
% 51.70/7.00  --dbg_dump_prop_clauses_file            -
% 51.70/7.00  --dbg_out_stat                          false
% 51.70/7.00  ------ Parsing...
% 51.70/7.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.70/7.00  
% 51.70/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 51.70/7.00  
% 51.70/7.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.70/7.00  
% 51.70/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.70/7.00  ------ Proving...
% 51.70/7.00  ------ Problem Properties 
% 51.70/7.00  
% 51.70/7.00  
% 51.70/7.00  clauses                                 13
% 51.70/7.00  conjectures                             3
% 51.70/7.00  EPR                                     0
% 51.70/7.00  Horn                                    13
% 51.70/7.00  unary                                   9
% 51.70/7.00  binary                                  4
% 51.70/7.00  lits                                    17
% 51.70/7.00  lits eq                                 7
% 51.70/7.00  fd_pure                                 0
% 51.70/7.00  fd_pseudo                               0
% 51.70/7.00  fd_cond                                 0
% 51.70/7.00  fd_pseudo_cond                          0
% 51.70/7.00  AC symbols                              0
% 51.70/7.00  
% 51.70/7.00  ------ Schedule dynamic 5 is on 
% 51.70/7.00  
% 51.70/7.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 51.70/7.00  
% 51.70/7.00  
% 51.70/7.00  ------ 
% 51.70/7.00  Current options:
% 51.70/7.00  ------ 
% 51.70/7.00  
% 51.70/7.00  ------ Input Options
% 51.70/7.00  
% 51.70/7.00  --out_options                           all
% 51.70/7.00  --tptp_safe_out                         true
% 51.70/7.00  --problem_path                          ""
% 51.70/7.00  --include_path                          ""
% 51.70/7.00  --clausifier                            res/vclausify_rel
% 51.70/7.00  --clausifier_options                    ""
% 51.70/7.00  --stdin                                 false
% 51.70/7.00  --stats_out                             all
% 51.70/7.00  
% 51.70/7.00  ------ General Options
% 51.70/7.00  
% 51.70/7.00  --fof                                   false
% 51.70/7.00  --time_out_real                         305.
% 51.70/7.00  --time_out_virtual                      -1.
% 51.70/7.00  --symbol_type_check                     false
% 51.70/7.00  --clausify_out                          false
% 51.70/7.00  --sig_cnt_out                           false
% 51.70/7.00  --trig_cnt_out                          false
% 51.70/7.00  --trig_cnt_out_tolerance                1.
% 51.70/7.00  --trig_cnt_out_sk_spl                   false
% 51.70/7.00  --abstr_cl_out                          false
% 51.70/7.00  
% 51.70/7.00  ------ Global Options
% 51.70/7.00  
% 51.70/7.00  --schedule                              default
% 51.70/7.00  --add_important_lit                     false
% 51.70/7.00  --prop_solver_per_cl                    1000
% 51.70/7.00  --min_unsat_core                        false
% 51.70/7.00  --soft_assumptions                      false
% 51.70/7.00  --soft_lemma_size                       3
% 51.70/7.00  --prop_impl_unit_size                   0
% 51.70/7.00  --prop_impl_unit                        []
% 51.70/7.00  --share_sel_clauses                     true
% 51.70/7.00  --reset_solvers                         false
% 51.70/7.00  --bc_imp_inh                            [conj_cone]
% 51.70/7.00  --conj_cone_tolerance                   3.
% 51.70/7.00  --extra_neg_conj                        none
% 51.70/7.00  --large_theory_mode                     true
% 51.70/7.00  --prolific_symb_bound                   200
% 51.70/7.00  --lt_threshold                          2000
% 51.70/7.00  --clause_weak_htbl                      true
% 51.70/7.00  --gc_record_bc_elim                     false
% 51.70/7.00  
% 51.70/7.00  ------ Preprocessing Options
% 51.70/7.00  
% 51.70/7.00  --preprocessing_flag                    true
% 51.70/7.00  --time_out_prep_mult                    0.1
% 51.70/7.00  --splitting_mode                        input
% 51.70/7.00  --splitting_grd                         true
% 51.70/7.00  --splitting_cvd                         false
% 51.70/7.00  --splitting_cvd_svl                     false
% 51.70/7.00  --splitting_nvd                         32
% 51.70/7.00  --sub_typing                            true
% 51.70/7.00  --prep_gs_sim                           true
% 51.70/7.00  --prep_unflatten                        true
% 51.70/7.00  --prep_res_sim                          true
% 51.70/7.00  --prep_upred                            true
% 51.70/7.00  --prep_sem_filter                       exhaustive
% 51.70/7.00  --prep_sem_filter_out                   false
% 51.70/7.00  --pred_elim                             true
% 51.70/7.00  --res_sim_input                         true
% 51.70/7.00  --eq_ax_congr_red                       true
% 51.70/7.00  --pure_diseq_elim                       true
% 51.70/7.00  --brand_transform                       false
% 51.70/7.00  --non_eq_to_eq                          false
% 51.70/7.00  --prep_def_merge                        true
% 51.70/7.00  --prep_def_merge_prop_impl              false
% 51.70/7.00  --prep_def_merge_mbd                    true
% 51.70/7.00  --prep_def_merge_tr_red                 false
% 51.70/7.00  --prep_def_merge_tr_cl                  false
% 51.70/7.00  --smt_preprocessing                     true
% 51.70/7.00  --smt_ac_axioms                         fast
% 51.70/7.00  --preprocessed_out                      false
% 51.70/7.00  --preprocessed_stats                    false
% 51.70/7.00  
% 51.70/7.00  ------ Abstraction refinement Options
% 51.70/7.00  
% 51.70/7.00  --abstr_ref                             []
% 51.70/7.00  --abstr_ref_prep                        false
% 51.70/7.00  --abstr_ref_until_sat                   false
% 51.70/7.00  --abstr_ref_sig_restrict                funpre
% 51.70/7.00  --abstr_ref_af_restrict_to_split_sk     false
% 51.70/7.00  --abstr_ref_under                       []
% 51.70/7.00  
% 51.70/7.00  ------ SAT Options
% 51.70/7.00  
% 51.70/7.00  --sat_mode                              false
% 51.70/7.00  --sat_fm_restart_options                ""
% 51.70/7.00  --sat_gr_def                            false
% 51.70/7.00  --sat_epr_types                         true
% 51.70/7.00  --sat_non_cyclic_types                  false
% 51.70/7.00  --sat_finite_models                     false
% 51.70/7.00  --sat_fm_lemmas                         false
% 51.70/7.00  --sat_fm_prep                           false
% 51.70/7.00  --sat_fm_uc_incr                        true
% 51.70/7.00  --sat_out_model                         small
% 51.70/7.00  --sat_out_clauses                       false
% 51.70/7.00  
% 51.70/7.00  ------ QBF Options
% 51.70/7.00  
% 51.70/7.00  --qbf_mode                              false
% 51.70/7.00  --qbf_elim_univ                         false
% 51.70/7.00  --qbf_dom_inst                          none
% 51.70/7.00  --qbf_dom_pre_inst                      false
% 51.70/7.00  --qbf_sk_in                             false
% 51.70/7.00  --qbf_pred_elim                         true
% 51.70/7.00  --qbf_split                             512
% 51.70/7.00  
% 51.70/7.00  ------ BMC1 Options
% 51.70/7.00  
% 51.70/7.00  --bmc1_incremental                      false
% 51.70/7.00  --bmc1_axioms                           reachable_all
% 51.70/7.00  --bmc1_min_bound                        0
% 51.70/7.00  --bmc1_max_bound                        -1
% 51.70/7.00  --bmc1_max_bound_default                -1
% 51.70/7.00  --bmc1_symbol_reachability              true
% 51.70/7.00  --bmc1_property_lemmas                  false
% 51.70/7.00  --bmc1_k_induction                      false
% 51.70/7.00  --bmc1_non_equiv_states                 false
% 51.70/7.00  --bmc1_deadlock                         false
% 51.70/7.00  --bmc1_ucm                              false
% 51.70/7.00  --bmc1_add_unsat_core                   none
% 51.70/7.00  --bmc1_unsat_core_children              false
% 51.70/7.00  --bmc1_unsat_core_extrapolate_axioms    false
% 51.70/7.00  --bmc1_out_stat                         full
% 51.70/7.00  --bmc1_ground_init                      false
% 51.70/7.00  --bmc1_pre_inst_next_state              false
% 51.70/7.00  --bmc1_pre_inst_state                   false
% 51.70/7.00  --bmc1_pre_inst_reach_state             false
% 51.70/7.00  --bmc1_out_unsat_core                   false
% 51.70/7.00  --bmc1_aig_witness_out                  false
% 51.70/7.00  --bmc1_verbose                          false
% 51.70/7.00  --bmc1_dump_clauses_tptp                false
% 51.70/7.00  --bmc1_dump_unsat_core_tptp             false
% 51.70/7.00  --bmc1_dump_file                        -
% 51.70/7.00  --bmc1_ucm_expand_uc_limit              128
% 51.70/7.00  --bmc1_ucm_n_expand_iterations          6
% 51.70/7.00  --bmc1_ucm_extend_mode                  1
% 51.70/7.00  --bmc1_ucm_init_mode                    2
% 51.70/7.00  --bmc1_ucm_cone_mode                    none
% 51.70/7.00  --bmc1_ucm_reduced_relation_type        0
% 51.70/7.00  --bmc1_ucm_relax_model                  4
% 51.70/7.00  --bmc1_ucm_full_tr_after_sat            true
% 51.70/7.00  --bmc1_ucm_expand_neg_assumptions       false
% 51.70/7.00  --bmc1_ucm_layered_model                none
% 51.70/7.00  --bmc1_ucm_max_lemma_size               10
% 51.70/7.00  
% 51.70/7.00  ------ AIG Options
% 51.70/7.00  
% 51.70/7.00  --aig_mode                              false
% 51.70/7.00  
% 51.70/7.00  ------ Instantiation Options
% 51.70/7.00  
% 51.70/7.00  --instantiation_flag                    true
% 51.70/7.00  --inst_sos_flag                         true
% 51.70/7.00  --inst_sos_phase                        true
% 51.70/7.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.70/7.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.70/7.00  --inst_lit_sel_side                     none
% 51.70/7.00  --inst_solver_per_active                1400
% 51.70/7.00  --inst_solver_calls_frac                1.
% 51.70/7.00  --inst_passive_queue_type               priority_queues
% 51.70/7.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.70/7.00  --inst_passive_queues_freq              [25;2]
% 51.70/7.00  --inst_dismatching                      true
% 51.70/7.00  --inst_eager_unprocessed_to_passive     true
% 51.70/7.00  --inst_prop_sim_given                   true
% 51.70/7.00  --inst_prop_sim_new                     false
% 51.70/7.00  --inst_subs_new                         false
% 51.70/7.00  --inst_eq_res_simp                      false
% 51.70/7.00  --inst_subs_given                       false
% 51.70/7.00  --inst_orphan_elimination               true
% 51.70/7.00  --inst_learning_loop_flag               true
% 51.70/7.00  --inst_learning_start                   3000
% 51.70/7.00  --inst_learning_factor                  2
% 51.70/7.00  --inst_start_prop_sim_after_learn       3
% 51.70/7.00  --inst_sel_renew                        solver
% 51.70/7.00  --inst_lit_activity_flag                true
% 51.70/7.00  --inst_restr_to_given                   false
% 51.70/7.00  --inst_activity_threshold               500
% 51.70/7.00  --inst_out_proof                        true
% 51.70/7.00  
% 51.70/7.00  ------ Resolution Options
% 51.70/7.00  
% 51.70/7.00  --resolution_flag                       false
% 51.70/7.00  --res_lit_sel                           adaptive
% 51.70/7.00  --res_lit_sel_side                      none
% 51.70/7.00  --res_ordering                          kbo
% 51.70/7.00  --res_to_prop_solver                    active
% 51.70/7.00  --res_prop_simpl_new                    false
% 51.70/7.00  --res_prop_simpl_given                  true
% 51.70/7.00  --res_passive_queue_type                priority_queues
% 51.70/7.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.70/7.00  --res_passive_queues_freq               [15;5]
% 51.70/7.00  --res_forward_subs                      full
% 51.70/7.00  --res_backward_subs                     full
% 51.70/7.00  --res_forward_subs_resolution           true
% 51.70/7.00  --res_backward_subs_resolution          true
% 51.70/7.00  --res_orphan_elimination                true
% 51.70/7.00  --res_time_limit                        2.
% 51.70/7.00  --res_out_proof                         true
% 51.70/7.00  
% 51.70/7.00  ------ Superposition Options
% 51.70/7.00  
% 51.70/7.00  --superposition_flag                    true
% 51.70/7.00  --sup_passive_queue_type                priority_queues
% 51.70/7.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.70/7.00  --sup_passive_queues_freq               [8;1;4]
% 51.70/7.00  --demod_completeness_check              fast
% 51.70/7.00  --demod_use_ground                      true
% 51.70/7.00  --sup_to_prop_solver                    passive
% 51.70/7.00  --sup_prop_simpl_new                    true
% 51.70/7.00  --sup_prop_simpl_given                  true
% 51.70/7.00  --sup_fun_splitting                     true
% 51.70/7.00  --sup_smt_interval                      50000
% 51.70/7.00  
% 51.70/7.00  ------ Superposition Simplification Setup
% 51.70/7.00  
% 51.70/7.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.70/7.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.70/7.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.70/7.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.70/7.00  --sup_full_triv                         [TrivRules;PropSubs]
% 51.70/7.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.70/7.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.70/7.00  --sup_immed_triv                        [TrivRules]
% 51.70/7.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.70/7.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.70/7.00  --sup_immed_bw_main                     []
% 51.70/7.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.70/7.00  --sup_input_triv                        [Unflattening;TrivRules]
% 51.70/7.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.70/7.00  --sup_input_bw                          []
% 51.70/7.00  
% 51.70/7.00  ------ Combination Options
% 51.70/7.00  
% 51.70/7.00  --comb_res_mult                         3
% 51.70/7.00  --comb_sup_mult                         2
% 51.70/7.00  --comb_inst_mult                        10
% 51.70/7.00  
% 51.70/7.00  ------ Debug Options
% 51.70/7.00  
% 51.70/7.00  --dbg_backtrace                         false
% 51.70/7.00  --dbg_dump_prop_clauses                 false
% 51.70/7.00  --dbg_dump_prop_clauses_file            -
% 51.70/7.00  --dbg_out_stat                          false
% 51.70/7.00  
% 51.70/7.00  
% 51.70/7.00  
% 51.70/7.00  
% 51.70/7.00  ------ Proving...
% 51.70/7.00  
% 51.70/7.00  
% 51.70/7.00  % SZS status Theorem for theBenchmark.p
% 51.70/7.00  
% 51.70/7.00  % SZS output start CNFRefutation for theBenchmark.p
% 51.70/7.00  
% 51.70/7.00  fof(f8,axiom,(
% 51.70/7.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 51.70/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.70/7.00  
% 51.70/7.00  fof(f28,plain,(
% 51.70/7.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 51.70/7.00    inference(cnf_transformation,[],[f8])).
% 51.70/7.00  
% 51.70/7.00  fof(f6,axiom,(
% 51.70/7.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 51.70/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.70/7.00  
% 51.70/7.00  fof(f26,plain,(
% 51.70/7.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 51.70/7.00    inference(cnf_transformation,[],[f6])).
% 51.70/7.00  
% 51.70/7.00  fof(f2,axiom,(
% 51.70/7.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 51.70/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.70/7.00  
% 51.70/7.00  fof(f17,plain,(
% 51.70/7.00    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 51.70/7.00    inference(nnf_transformation,[],[f2])).
% 51.70/7.00  
% 51.70/7.00  fof(f22,plain,(
% 51.70/7.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 51.70/7.00    inference(cnf_transformation,[],[f17])).
% 51.70/7.00  
% 51.70/7.00  fof(f3,axiom,(
% 51.70/7.00    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 51.70/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.70/7.00  
% 51.70/7.00  fof(f23,plain,(
% 51.70/7.00    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 51.70/7.00    inference(cnf_transformation,[],[f3])).
% 51.70/7.00  
% 51.70/7.00  fof(f1,axiom,(
% 51.70/7.00    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 51.70/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.70/7.00  
% 51.70/7.00  fof(f20,plain,(
% 51.70/7.00    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 51.70/7.00    inference(cnf_transformation,[],[f1])).
% 51.70/7.00  
% 51.70/7.00  fof(f34,plain,(
% 51.70/7.00    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 51.70/7.00    inference(definition_unfolding,[],[f23,f20])).
% 51.70/7.00  
% 51.70/7.00  fof(f9,axiom,(
% 51.70/7.00    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 51.70/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.70/7.00  
% 51.70/7.00  fof(f29,plain,(
% 51.70/7.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 51.70/7.00    inference(cnf_transformation,[],[f9])).
% 51.70/7.00  
% 51.70/7.00  fof(f11,conjecture,(
% 51.70/7.00    ! [X0,X1,X2] : ((r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2)) => r1_tarski(k5_xboole_0(X0,X1),X2))),
% 51.70/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.70/7.00  
% 51.70/7.00  fof(f12,negated_conjecture,(
% 51.70/7.00    ~! [X0,X1,X2] : ((r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2)) => r1_tarski(k5_xboole_0(X0,X1),X2))),
% 51.70/7.00    inference(negated_conjecture,[],[f11])).
% 51.70/7.00  
% 51.70/7.00  fof(f15,plain,(
% 51.70/7.00    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X1),X2) & (r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2)))),
% 51.70/7.00    inference(ennf_transformation,[],[f12])).
% 51.70/7.00  
% 51.70/7.00  fof(f16,plain,(
% 51.70/7.00    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X1),X2) & r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2))),
% 51.70/7.00    inference(flattening,[],[f15])).
% 51.70/7.00  
% 51.70/7.00  fof(f18,plain,(
% 51.70/7.00    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X1),X2) & r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2)) => (~r1_tarski(k5_xboole_0(sK0,sK1),sK2) & r1_tarski(k4_xboole_0(sK1,sK0),sK2) & r1_tarski(k4_xboole_0(sK0,sK1),sK2))),
% 51.70/7.00    introduced(choice_axiom,[])).
% 51.70/7.00  
% 51.70/7.00  fof(f19,plain,(
% 51.70/7.00    ~r1_tarski(k5_xboole_0(sK0,sK1),sK2) & r1_tarski(k4_xboole_0(sK1,sK0),sK2) & r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 51.70/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).
% 51.70/7.00  
% 51.70/7.00  fof(f32,plain,(
% 51.70/7.00    r1_tarski(k4_xboole_0(sK1,sK0),sK2)),
% 51.70/7.00    inference(cnf_transformation,[],[f19])).
% 51.70/7.00  
% 51.70/7.00  fof(f4,axiom,(
% 51.70/7.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 51.70/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.70/7.00  
% 51.70/7.00  fof(f13,plain,(
% 51.70/7.00    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 51.70/7.00    inference(ennf_transformation,[],[f4])).
% 51.70/7.00  
% 51.70/7.00  fof(f24,plain,(
% 51.70/7.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 51.70/7.00    inference(cnf_transformation,[],[f13])).
% 51.70/7.00  
% 51.70/7.00  fof(f31,plain,(
% 51.70/7.00    r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 51.70/7.00    inference(cnf_transformation,[],[f19])).
% 51.70/7.00  
% 51.70/7.00  fof(f10,axiom,(
% 51.70/7.00    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 51.70/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.70/7.00  
% 51.70/7.00  fof(f14,plain,(
% 51.70/7.00    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 51.70/7.00    inference(ennf_transformation,[],[f10])).
% 51.70/7.00  
% 51.70/7.00  fof(f30,plain,(
% 51.70/7.00    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 51.70/7.00    inference(cnf_transformation,[],[f14])).
% 51.70/7.00  
% 51.70/7.00  fof(f7,axiom,(
% 51.70/7.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 51.70/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.70/7.00  
% 51.70/7.00  fof(f27,plain,(
% 51.70/7.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 51.70/7.00    inference(cnf_transformation,[],[f7])).
% 51.70/7.00  
% 51.70/7.00  fof(f33,plain,(
% 51.70/7.00    ~r1_tarski(k5_xboole_0(sK0,sK1),sK2)),
% 51.70/7.00    inference(cnf_transformation,[],[f19])).
% 51.70/7.00  
% 51.70/7.00  fof(f35,plain,(
% 51.70/7.00    ~r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2)),
% 51.70/7.00    inference(definition_unfolding,[],[f33,f20])).
% 51.70/7.00  
% 51.70/7.00  cnf(c_7,plain,
% 51.70/7.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 51.70/7.00      inference(cnf_transformation,[],[f28]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_5,plain,
% 51.70/7.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 51.70/7.00      inference(cnf_transformation,[],[f26]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_353,plain,
% 51.70/7.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 51.70/7.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_512,plain,
% 51.70/7.00      ( r1_tarski(X0,X0) = iProver_top ),
% 51.70/7.00      inference(superposition,[status(thm)],[c_7,c_353]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_0,plain,
% 51.70/7.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 51.70/7.00      inference(cnf_transformation,[],[f22]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_357,plain,
% 51.70/7.00      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 51.70/7.00      | r1_tarski(X0,X1) != iProver_top ),
% 51.70/7.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_1890,plain,
% 51.70/7.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 51.70/7.00      inference(superposition,[status(thm)],[c_512,c_357]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_2,plain,
% 51.70/7.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 51.70/7.00      inference(cnf_transformation,[],[f34]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_8,plain,
% 51.70/7.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 51.70/7.00      inference(cnf_transformation,[],[f29]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_11,negated_conjecture,
% 51.70/7.00      ( r1_tarski(k4_xboole_0(sK1,sK0),sK2) ),
% 51.70/7.00      inference(cnf_transformation,[],[f32]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_350,plain,
% 51.70/7.00      ( r1_tarski(k4_xboole_0(sK1,sK0),sK2) = iProver_top ),
% 51.70/7.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_3,plain,
% 51.70/7.00      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 51.70/7.00      inference(cnf_transformation,[],[f24]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_355,plain,
% 51.70/7.00      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 51.70/7.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_941,plain,
% 51.70/7.00      ( k2_xboole_0(k4_xboole_0(sK1,sK0),sK2) = sK2 ),
% 51.70/7.00      inference(superposition,[status(thm)],[c_350,c_355]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_695,plain,
% 51.70/7.00      ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = iProver_top ),
% 51.70/7.00      inference(superposition,[status(thm)],[c_8,c_353]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_949,plain,
% 51.70/7.00      ( r1_tarski(k4_xboole_0(X0,sK2),k4_xboole_0(X0,k4_xboole_0(sK1,sK0))) = iProver_top ),
% 51.70/7.00      inference(superposition,[status(thm)],[c_941,c_695]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_1022,plain,
% 51.70/7.00      ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,X1),sK2),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(sK1,sK0)))) = iProver_top ),
% 51.70/7.00      inference(superposition,[status(thm)],[c_8,c_949]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_1024,plain,
% 51.70/7.00      ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,sK2)),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(sK1,sK0)))) = iProver_top ),
% 51.70/7.00      inference(demodulation,[status(thm)],[c_1022,c_8]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_15010,plain,
% 51.70/7.00      ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)),k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))) = iProver_top ),
% 51.70/7.00      inference(superposition,[status(thm)],[c_2,c_1024]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_12,negated_conjecture,
% 51.70/7.00      ( r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
% 51.70/7.00      inference(cnf_transformation,[],[f31]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_349,plain,
% 51.70/7.00      ( r1_tarski(k4_xboole_0(sK0,sK1),sK2) = iProver_top ),
% 51.70/7.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_942,plain,
% 51.70/7.00      ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) = sK2 ),
% 51.70/7.00      inference(superposition,[status(thm)],[c_349,c_355]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_15038,plain,
% 51.70/7.00      ( r1_tarski(k4_xboole_0(X0,sK2),k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))) = iProver_top ),
% 51.70/7.00      inference(light_normalisation,[status(thm)],[c_15010,c_942]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_9,plain,
% 51.70/7.00      ( r1_tarski(X0,k2_xboole_0(X1,X2))
% 51.70/7.00      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 51.70/7.00      inference(cnf_transformation,[],[f30]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_352,plain,
% 51.70/7.00      ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
% 51.70/7.00      | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
% 51.70/7.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_15292,plain,
% 51.70/7.00      ( r1_tarski(X0,k2_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))))) = iProver_top ),
% 51.70/7.00      inference(superposition,[status(thm)],[c_15038,c_352]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_154092,plain,
% 51.70/7.00      ( r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(sK2,k1_xboole_0)) = iProver_top ),
% 51.70/7.00      inference(superposition,[status(thm)],[c_1890,c_15292]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_1887,plain,
% 51.70/7.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 51.70/7.00      inference(superposition,[status(thm)],[c_353,c_357]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_6,plain,
% 51.70/7.00      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 51.70/7.00      inference(cnf_transformation,[],[f27]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_143291,plain,
% 51.70/7.00      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 51.70/7.00      inference(superposition,[status(thm)],[c_1887,c_6]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_940,plain,
% 51.70/7.00      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 51.70/7.00      inference(superposition,[status(thm)],[c_353,c_355]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_697,plain,
% 51.70/7.00      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 51.70/7.00      inference(superposition,[status(thm)],[c_8,c_6]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_20398,plain,
% 51.70/7.00      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 51.70/7.00      inference(superposition,[status(thm)],[c_940,c_697]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_20430,plain,
% 51.70/7.00      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,X1) ),
% 51.70/7.00      inference(light_normalisation,[status(thm)],[c_20398,c_6]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_146431,plain,
% 51.70/7.00      ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
% 51.70/7.00      inference(superposition,[status(thm)],[c_143291,c_20430]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_943,plain,
% 51.70/7.00      ( k2_xboole_0(X0,X0) = X0 ),
% 51.70/7.00      inference(superposition,[status(thm)],[c_512,c_355]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_146503,plain,
% 51.70/7.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 51.70/7.00      inference(light_normalisation,[status(thm)],[c_146431,c_943]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_154309,plain,
% 51.70/7.00      ( r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK2) = iProver_top ),
% 51.70/7.00      inference(demodulation,[status(thm)],[c_154092,c_146503]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_10,negated_conjecture,
% 51.70/7.00      ( ~ r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2) ),
% 51.70/7.00      inference(cnf_transformation,[],[f35]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_351,plain,
% 51.70/7.00      ( r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2) != iProver_top ),
% 51.70/7.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(c_475,plain,
% 51.70/7.00      ( r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK2) != iProver_top ),
% 51.70/7.00      inference(demodulation,[status(thm)],[c_351,c_2]) ).
% 51.70/7.00  
% 51.70/7.00  cnf(contradiction,plain,
% 51.70/7.00      ( $false ),
% 51.70/7.00      inference(minisat,[status(thm)],[c_154309,c_475]) ).
% 51.70/7.00  
% 51.70/7.00  
% 51.70/7.00  % SZS output end CNFRefutation for theBenchmark.p
% 51.70/7.00  
% 51.70/7.00  ------                               Statistics
% 51.70/7.00  
% 51.70/7.00  ------ General
% 51.70/7.00  
% 51.70/7.00  abstr_ref_over_cycles:                  0
% 51.70/7.00  abstr_ref_under_cycles:                 0
% 51.70/7.00  gc_basic_clause_elim:                   0
% 51.70/7.00  forced_gc_time:                         0
% 51.70/7.00  parsing_time:                           0.007
% 51.70/7.00  unif_index_cands_time:                  0.
% 51.70/7.00  unif_index_add_time:                    0.
% 51.70/7.00  orderings_time:                         0.
% 51.70/7.00  out_proof_time:                         0.014
% 51.70/7.00  total_time:                             6.201
% 51.70/7.00  num_of_symbols:                         39
% 51.70/7.00  num_of_terms:                           304721
% 51.70/7.00  
% 51.70/7.00  ------ Preprocessing
% 51.70/7.00  
% 51.70/7.00  num_of_splits:                          0
% 51.70/7.00  num_of_split_atoms:                     0
% 51.70/7.00  num_of_reused_defs:                     0
% 51.70/7.00  num_eq_ax_congr_red:                    4
% 51.70/7.00  num_of_sem_filtered_clauses:            1
% 51.70/7.00  num_of_subtypes:                        0
% 51.70/7.00  monotx_restored_types:                  0
% 51.70/7.00  sat_num_of_epr_types:                   0
% 51.70/7.00  sat_num_of_non_cyclic_types:            0
% 51.70/7.00  sat_guarded_non_collapsed_types:        0
% 51.70/7.00  num_pure_diseq_elim:                    0
% 51.70/7.00  simp_replaced_by:                       0
% 51.70/7.00  res_preprocessed:                       50
% 51.70/7.00  prep_upred:                             0
% 51.70/7.00  prep_unflattend:                        0
% 51.70/7.00  smt_new_axioms:                         0
% 51.70/7.00  pred_elim_cands:                        1
% 51.70/7.00  pred_elim:                              0
% 51.70/7.00  pred_elim_cl:                           0
% 51.70/7.00  pred_elim_cycles:                       1
% 51.70/7.00  merged_defs:                            6
% 51.70/7.00  merged_defs_ncl:                        0
% 51.70/7.00  bin_hyper_res:                          6
% 51.70/7.00  prep_cycles:                            3
% 51.70/7.00  pred_elim_time:                         0.
% 51.70/7.00  splitting_time:                         0.
% 51.70/7.00  sem_filter_time:                        0.
% 51.70/7.00  monotx_time:                            0.
% 51.70/7.00  subtype_inf_time:                       0.
% 51.70/7.00  
% 51.70/7.00  ------ Problem properties
% 51.70/7.00  
% 51.70/7.00  clauses:                                13
% 51.70/7.00  conjectures:                            3
% 51.70/7.00  epr:                                    0
% 51.70/7.00  horn:                                   13
% 51.70/7.00  ground:                                 3
% 51.70/7.00  unary:                                  9
% 51.70/7.00  binary:                                 4
% 51.70/7.00  lits:                                   17
% 51.70/7.00  lits_eq:                                7
% 51.70/7.00  fd_pure:                                0
% 51.70/7.00  fd_pseudo:                              0
% 51.70/7.00  fd_cond:                                0
% 51.70/7.00  fd_pseudo_cond:                         0
% 51.70/7.00  ac_symbols:                             0
% 51.70/7.00  
% 51.70/7.00  ------ Propositional Solver
% 51.70/7.00  
% 51.70/7.00  prop_solver_calls:                      50
% 51.70/7.00  prop_fast_solver_calls:                 785
% 51.70/7.00  smt_solver_calls:                       0
% 51.70/7.00  smt_fast_solver_calls:                  0
% 51.70/7.00  prop_num_of_clauses:                    49548
% 51.70/7.00  prop_preprocess_simplified:             35627
% 51.70/7.00  prop_fo_subsumed:                       3
% 51.70/7.00  prop_solver_time:                       0.
% 51.70/7.00  smt_solver_time:                        0.
% 51.70/7.00  smt_fast_solver_time:                   0.
% 51.70/7.00  prop_fast_solver_time:                  0.
% 51.70/7.00  prop_unsat_core_time:                   0.005
% 51.70/7.00  
% 51.70/7.00  ------ QBF
% 51.70/7.00  
% 51.70/7.00  qbf_q_res:                              0
% 51.70/7.00  qbf_num_tautologies:                    0
% 51.70/7.00  qbf_prep_cycles:                        0
% 51.70/7.00  
% 51.70/7.00  ------ BMC1
% 51.70/7.00  
% 51.70/7.00  bmc1_current_bound:                     -1
% 51.70/7.00  bmc1_last_solved_bound:                 -1
% 51.70/7.00  bmc1_unsat_core_size:                   -1
% 51.70/7.00  bmc1_unsat_core_parents_size:           -1
% 51.70/7.00  bmc1_merge_next_fun:                    0
% 51.70/7.00  bmc1_unsat_core_clauses_time:           0.
% 51.70/7.00  
% 51.70/7.00  ------ Instantiation
% 51.70/7.00  
% 51.70/7.00  inst_num_of_clauses:                    7602
% 51.70/7.00  inst_num_in_passive:                    3443
% 51.70/7.00  inst_num_in_active:                     2295
% 51.70/7.00  inst_num_in_unprocessed:                1868
% 51.70/7.00  inst_num_of_loops:                      2690
% 51.70/7.00  inst_num_of_learning_restarts:          0
% 51.70/7.00  inst_num_moves_active_passive:          389
% 51.70/7.00  inst_lit_activity:                      0
% 51.70/7.00  inst_lit_activity_moves:                2
% 51.70/7.00  inst_num_tautologies:                   0
% 51.70/7.00  inst_num_prop_implied:                  0
% 51.70/7.00  inst_num_existing_simplified:           0
% 51.70/7.00  inst_num_eq_res_simplified:             0
% 51.70/7.00  inst_num_child_elim:                    0
% 51.70/7.00  inst_num_of_dismatching_blockings:      6999
% 51.70/7.00  inst_num_of_non_proper_insts:           8807
% 51.70/7.00  inst_num_of_duplicates:                 0
% 51.70/7.00  inst_inst_num_from_inst_to_res:         0
% 51.70/7.00  inst_dismatching_checking_time:         0.
% 51.70/7.00  
% 51.70/7.00  ------ Resolution
% 51.70/7.00  
% 51.70/7.00  res_num_of_clauses:                     0
% 51.70/7.00  res_num_in_passive:                     0
% 51.70/7.00  res_num_in_active:                      0
% 51.70/7.00  res_num_of_loops:                       53
% 51.70/7.00  res_forward_subset_subsumed:            762
% 51.70/7.00  res_backward_subset_subsumed:           20
% 51.70/7.00  res_forward_subsumed:                   0
% 51.70/7.00  res_backward_subsumed:                  0
% 51.70/7.00  res_forward_subsumption_resolution:     0
% 51.70/7.00  res_backward_subsumption_resolution:    0
% 51.70/7.00  res_clause_to_clause_subsumption:       154049
% 51.70/7.00  res_orphan_elimination:                 0
% 51.70/7.00  res_tautology_del:                      337
% 51.70/7.00  res_num_eq_res_simplified:              0
% 51.70/7.00  res_num_sel_changes:                    0
% 51.70/7.00  res_moves_from_active_to_pass:          0
% 51.70/7.00  
% 51.70/7.00  ------ Superposition
% 51.70/7.00  
% 51.70/7.00  sup_time_total:                         0.
% 51.70/7.00  sup_time_generating:                    0.
% 51.70/7.00  sup_time_sim_full:                      0.
% 51.70/7.00  sup_time_sim_immed:                     0.
% 51.70/7.00  
% 51.70/7.00  sup_num_of_clauses:                     9883
% 51.70/7.00  sup_num_in_active:                      490
% 51.70/7.00  sup_num_in_passive:                     9393
% 51.70/7.00  sup_num_of_loops:                       536
% 51.70/7.00  sup_fw_superposition:                   24965
% 51.70/7.00  sup_bw_superposition:                   13677
% 51.70/7.00  sup_immediate_simplified:               31873
% 51.70/7.00  sup_given_eliminated:                   4
% 51.70/7.00  comparisons_done:                       0
% 51.70/7.00  comparisons_avoided:                    0
% 51.70/7.00  
% 51.70/7.00  ------ Simplifications
% 51.70/7.00  
% 51.70/7.00  
% 51.70/7.00  sim_fw_subset_subsumed:                 25
% 51.70/7.00  sim_bw_subset_subsumed:                 21
% 51.70/7.00  sim_fw_subsumed:                        4774
% 51.70/7.00  sim_bw_subsumed:                        305
% 51.70/7.00  sim_fw_subsumption_res:                 0
% 51.70/7.00  sim_bw_subsumption_res:                 0
% 51.70/7.00  sim_tautology_del:                      19
% 51.70/7.00  sim_eq_tautology_del:                   3233
% 51.70/7.00  sim_eq_res_simp:                        16
% 51.70/7.00  sim_fw_demodulated:                     35576
% 51.70/7.00  sim_bw_demodulated:                     738
% 51.70/7.00  sim_light_normalised:                   12330
% 51.70/7.00  sim_joinable_taut:                      0
% 51.70/7.00  sim_joinable_simp:                      0
% 51.70/7.00  sim_ac_normalised:                      0
% 51.70/7.00  sim_smt_subsumption:                    0
% 51.70/7.00  
%------------------------------------------------------------------------------
