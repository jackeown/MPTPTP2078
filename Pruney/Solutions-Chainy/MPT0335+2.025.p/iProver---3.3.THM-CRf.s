%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:29 EST 2020

% Result     : Theorem 3.94s
% Output     : CNFRefutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 238 expanded)
%              Number of clauses        :   32 (  52 expanded)
%              Number of leaves         :   11 (  69 expanded)
%              Depth                    :   15
%              Number of atoms          :  115 ( 435 expanded)
%              Number of equality atoms :   79 ( 296 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f27,plain,
    ( ? [X0,X1,X2,X3] :
        ( k3_xboole_0(X0,X2) != k1_tarski(X3)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK2,sK4) != k1_tarski(sK5)
      & r2_hidden(sK5,sK2)
      & k3_xboole_0(sK3,sK4) = k1_tarski(sK5)
      & r1_tarski(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( k3_xboole_0(sK2,sK4) != k1_tarski(sK5)
    & r2_hidden(sK5,sK2)
    & k3_xboole_0(sK3,sK4) = k1_tarski(sK5)
    & r1_tarski(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f16,f27])).

fof(f49,plain,(
    r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f29,f41,f41])).

fof(f48,plain,(
    k3_xboole_0(sK3,sK4) = k1_tarski(sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f51])).

fof(f59,plain,(
    k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(definition_unfolding,[],[f48,f41,f52])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f52])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f39,f41,f41,f41,f41])).

fof(f47,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f50,plain,(
    k3_xboole_0(sK2,sK4) != k1_tarski(sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f58,plain,(
    k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(definition_unfolding,[],[f50,f41,f52])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_689,plain,
    ( r2_hidden(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_16,negated_conjecture,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_709,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) ),
    inference(demodulation,[status(thm)],[c_0,c_16])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_691,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2000,plain,
    ( r2_hidden(sK5,X0) != iProver_top
    | r1_tarski(k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_709,c_691])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_692,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3334,plain,
    ( k4_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)),k4_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)),X0)) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK3))
    | r2_hidden(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2000,c_692])).

cnf(c_10,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3338,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK3))
    | r2_hidden(sK5,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3334,c_10])).

cnf(c_15468,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)))) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) ),
    inference(superposition,[status(thm)],[c_689,c_3338])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_688,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_877,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = sK2 ),
    inference(superposition,[status(thm)],[c_688,c_692])).

cnf(c_1096,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_0,c_10])).

cnf(c_2709,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_877,c_1096])).

cnf(c_1112,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_877,c_10])).

cnf(c_1474,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,sK3)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_1112])).

cnf(c_3783,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_2709,c_1474])).

cnf(c_3844,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_3783,c_877])).

cnf(c_15483,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_15468,c_3844])).

cnf(c_16738,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) ),
    inference(demodulation,[status(thm)],[c_15483,c_709])).

cnf(c_1830,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_348,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1079,plain,
    ( k2_enumset1(X0,X1,X2,X3) != X4
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != X4
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(instantiation,[status(thm)],[c_348])).

cnf(c_1829,plain,
    ( k2_enumset1(X0,X1,X2,X3) != k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k2_enumset1(X0,X1,X2,X3)
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) ),
    inference(instantiation,[status(thm)],[c_1079])).

cnf(c_1831,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) != k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k2_enumset1(sK5,sK5,sK5,sK5)
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) ),
    inference(instantiation,[status(thm)],[c_1829])).

cnf(c_14,negated_conjecture,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(cnf_transformation,[],[f58])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16738,c_1830,c_1831,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n001.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 12:03:14 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.94/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/1.00  
% 3.94/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.94/1.00  
% 3.94/1.00  ------  iProver source info
% 3.94/1.00  
% 3.94/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.94/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.94/1.00  git: non_committed_changes: false
% 3.94/1.00  git: last_make_outside_of_git: false
% 3.94/1.00  
% 3.94/1.00  ------ 
% 3.94/1.00  
% 3.94/1.00  ------ Input Options
% 3.94/1.00  
% 3.94/1.00  --out_options                           all
% 3.94/1.00  --tptp_safe_out                         true
% 3.94/1.00  --problem_path                          ""
% 3.94/1.00  --include_path                          ""
% 3.94/1.00  --clausifier                            res/vclausify_rel
% 3.94/1.00  --clausifier_options                    --mode clausify
% 3.94/1.00  --stdin                                 false
% 3.94/1.00  --stats_out                             all
% 3.94/1.00  
% 3.94/1.00  ------ General Options
% 3.94/1.00  
% 3.94/1.00  --fof                                   false
% 3.94/1.00  --time_out_real                         305.
% 3.94/1.00  --time_out_virtual                      -1.
% 3.94/1.00  --symbol_type_check                     false
% 3.94/1.00  --clausify_out                          false
% 3.94/1.00  --sig_cnt_out                           false
% 3.94/1.00  --trig_cnt_out                          false
% 3.94/1.00  --trig_cnt_out_tolerance                1.
% 3.94/1.00  --trig_cnt_out_sk_spl                   false
% 3.94/1.00  --abstr_cl_out                          false
% 3.94/1.00  
% 3.94/1.00  ------ Global Options
% 3.94/1.00  
% 3.94/1.00  --schedule                              default
% 3.94/1.00  --add_important_lit                     false
% 3.94/1.00  --prop_solver_per_cl                    1000
% 3.94/1.00  --min_unsat_core                        false
% 3.94/1.00  --soft_assumptions                      false
% 3.94/1.00  --soft_lemma_size                       3
% 3.94/1.00  --prop_impl_unit_size                   0
% 3.94/1.00  --prop_impl_unit                        []
% 3.94/1.00  --share_sel_clauses                     true
% 3.94/1.00  --reset_solvers                         false
% 3.94/1.00  --bc_imp_inh                            [conj_cone]
% 3.94/1.00  --conj_cone_tolerance                   3.
% 3.94/1.00  --extra_neg_conj                        none
% 3.94/1.00  --large_theory_mode                     true
% 3.94/1.00  --prolific_symb_bound                   200
% 3.94/1.00  --lt_threshold                          2000
% 3.94/1.00  --clause_weak_htbl                      true
% 3.94/1.00  --gc_record_bc_elim                     false
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing Options
% 3.94/1.00  
% 3.94/1.00  --preprocessing_flag                    true
% 3.94/1.00  --time_out_prep_mult                    0.1
% 3.94/1.00  --splitting_mode                        input
% 3.94/1.00  --splitting_grd                         true
% 3.94/1.00  --splitting_cvd                         false
% 3.94/1.00  --splitting_cvd_svl                     false
% 3.94/1.00  --splitting_nvd                         32
% 3.94/1.00  --sub_typing                            true
% 3.94/1.00  --prep_gs_sim                           true
% 3.94/1.00  --prep_unflatten                        true
% 3.94/1.00  --prep_res_sim                          true
% 3.94/1.00  --prep_upred                            true
% 3.94/1.00  --prep_sem_filter                       exhaustive
% 3.94/1.00  --prep_sem_filter_out                   false
% 3.94/1.00  --pred_elim                             true
% 3.94/1.00  --res_sim_input                         true
% 3.94/1.00  --eq_ax_congr_red                       true
% 3.94/1.00  --pure_diseq_elim                       true
% 3.94/1.00  --brand_transform                       false
% 3.94/1.00  --non_eq_to_eq                          false
% 3.94/1.00  --prep_def_merge                        true
% 3.94/1.00  --prep_def_merge_prop_impl              false
% 3.94/1.00  --prep_def_merge_mbd                    true
% 3.94/1.00  --prep_def_merge_tr_red                 false
% 3.94/1.00  --prep_def_merge_tr_cl                  false
% 3.94/1.00  --smt_preprocessing                     true
% 3.94/1.00  --smt_ac_axioms                         fast
% 3.94/1.00  --preprocessed_out                      false
% 3.94/1.00  --preprocessed_stats                    false
% 3.94/1.00  
% 3.94/1.00  ------ Abstraction refinement Options
% 3.94/1.00  
% 3.94/1.00  --abstr_ref                             []
% 3.94/1.00  --abstr_ref_prep                        false
% 3.94/1.00  --abstr_ref_until_sat                   false
% 3.94/1.00  --abstr_ref_sig_restrict                funpre
% 3.94/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.94/1.00  --abstr_ref_under                       []
% 3.94/1.00  
% 3.94/1.00  ------ SAT Options
% 3.94/1.00  
% 3.94/1.00  --sat_mode                              false
% 3.94/1.00  --sat_fm_restart_options                ""
% 3.94/1.00  --sat_gr_def                            false
% 3.94/1.00  --sat_epr_types                         true
% 3.94/1.00  --sat_non_cyclic_types                  false
% 3.94/1.00  --sat_finite_models                     false
% 3.94/1.00  --sat_fm_lemmas                         false
% 3.94/1.00  --sat_fm_prep                           false
% 3.94/1.00  --sat_fm_uc_incr                        true
% 3.94/1.00  --sat_out_model                         small
% 3.94/1.00  --sat_out_clauses                       false
% 3.94/1.00  
% 3.94/1.00  ------ QBF Options
% 3.94/1.00  
% 3.94/1.00  --qbf_mode                              false
% 3.94/1.00  --qbf_elim_univ                         false
% 3.94/1.00  --qbf_dom_inst                          none
% 3.94/1.00  --qbf_dom_pre_inst                      false
% 3.94/1.00  --qbf_sk_in                             false
% 3.94/1.00  --qbf_pred_elim                         true
% 3.94/1.00  --qbf_split                             512
% 3.94/1.00  
% 3.94/1.00  ------ BMC1 Options
% 3.94/1.00  
% 3.94/1.00  --bmc1_incremental                      false
% 3.94/1.00  --bmc1_axioms                           reachable_all
% 3.94/1.00  --bmc1_min_bound                        0
% 3.94/1.00  --bmc1_max_bound                        -1
% 3.94/1.00  --bmc1_max_bound_default                -1
% 3.94/1.00  --bmc1_symbol_reachability              true
% 3.94/1.00  --bmc1_property_lemmas                  false
% 3.94/1.00  --bmc1_k_induction                      false
% 3.94/1.00  --bmc1_non_equiv_states                 false
% 3.94/1.00  --bmc1_deadlock                         false
% 3.94/1.00  --bmc1_ucm                              false
% 3.94/1.00  --bmc1_add_unsat_core                   none
% 3.94/1.00  --bmc1_unsat_core_children              false
% 3.94/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.94/1.00  --bmc1_out_stat                         full
% 3.94/1.00  --bmc1_ground_init                      false
% 3.94/1.00  --bmc1_pre_inst_next_state              false
% 3.94/1.00  --bmc1_pre_inst_state                   false
% 3.94/1.00  --bmc1_pre_inst_reach_state             false
% 3.94/1.00  --bmc1_out_unsat_core                   false
% 3.94/1.00  --bmc1_aig_witness_out                  false
% 3.94/1.00  --bmc1_verbose                          false
% 3.94/1.00  --bmc1_dump_clauses_tptp                false
% 3.94/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.94/1.00  --bmc1_dump_file                        -
% 3.94/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.94/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.94/1.00  --bmc1_ucm_extend_mode                  1
% 3.94/1.00  --bmc1_ucm_init_mode                    2
% 3.94/1.00  --bmc1_ucm_cone_mode                    none
% 3.94/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.94/1.00  --bmc1_ucm_relax_model                  4
% 3.94/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.94/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.94/1.00  --bmc1_ucm_layered_model                none
% 3.94/1.00  --bmc1_ucm_max_lemma_size               10
% 3.94/1.00  
% 3.94/1.00  ------ AIG Options
% 3.94/1.00  
% 3.94/1.00  --aig_mode                              false
% 3.94/1.00  
% 3.94/1.00  ------ Instantiation Options
% 3.94/1.00  
% 3.94/1.00  --instantiation_flag                    true
% 3.94/1.00  --inst_sos_flag                         false
% 3.94/1.00  --inst_sos_phase                        true
% 3.94/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.94/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.94/1.00  --inst_lit_sel_side                     num_symb
% 3.94/1.00  --inst_solver_per_active                1400
% 3.94/1.00  --inst_solver_calls_frac                1.
% 3.94/1.00  --inst_passive_queue_type               priority_queues
% 3.94/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.94/1.00  --inst_passive_queues_freq              [25;2]
% 3.94/1.00  --inst_dismatching                      true
% 3.94/1.00  --inst_eager_unprocessed_to_passive     true
% 3.94/1.00  --inst_prop_sim_given                   true
% 3.94/1.00  --inst_prop_sim_new                     false
% 3.94/1.00  --inst_subs_new                         false
% 3.94/1.00  --inst_eq_res_simp                      false
% 3.94/1.00  --inst_subs_given                       false
% 3.94/1.00  --inst_orphan_elimination               true
% 3.94/1.00  --inst_learning_loop_flag               true
% 3.94/1.00  --inst_learning_start                   3000
% 3.94/1.00  --inst_learning_factor                  2
% 3.94/1.00  --inst_start_prop_sim_after_learn       3
% 3.94/1.00  --inst_sel_renew                        solver
% 3.94/1.00  --inst_lit_activity_flag                true
% 3.94/1.00  --inst_restr_to_given                   false
% 3.94/1.00  --inst_activity_threshold               500
% 3.94/1.00  --inst_out_proof                        true
% 3.94/1.00  
% 3.94/1.00  ------ Resolution Options
% 3.94/1.00  
% 3.94/1.00  --resolution_flag                       true
% 3.94/1.00  --res_lit_sel                           adaptive
% 3.94/1.00  --res_lit_sel_side                      none
% 3.94/1.00  --res_ordering                          kbo
% 3.94/1.00  --res_to_prop_solver                    active
% 3.94/1.00  --res_prop_simpl_new                    false
% 3.94/1.00  --res_prop_simpl_given                  true
% 3.94/1.00  --res_passive_queue_type                priority_queues
% 3.94/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.94/1.00  --res_passive_queues_freq               [15;5]
% 3.94/1.00  --res_forward_subs                      full
% 3.94/1.00  --res_backward_subs                     full
% 3.94/1.00  --res_forward_subs_resolution           true
% 3.94/1.00  --res_backward_subs_resolution          true
% 3.94/1.00  --res_orphan_elimination                true
% 3.94/1.00  --res_time_limit                        2.
% 3.94/1.00  --res_out_proof                         true
% 3.94/1.00  
% 3.94/1.00  ------ Superposition Options
% 3.94/1.00  
% 3.94/1.00  --superposition_flag                    true
% 3.94/1.00  --sup_passive_queue_type                priority_queues
% 3.94/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.94/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.94/1.00  --demod_completeness_check              fast
% 3.94/1.00  --demod_use_ground                      true
% 3.94/1.00  --sup_to_prop_solver                    passive
% 3.94/1.00  --sup_prop_simpl_new                    true
% 3.94/1.00  --sup_prop_simpl_given                  true
% 3.94/1.00  --sup_fun_splitting                     false
% 3.94/1.00  --sup_smt_interval                      50000
% 3.94/1.00  
% 3.94/1.00  ------ Superposition Simplification Setup
% 3.94/1.00  
% 3.94/1.00  --sup_indices_passive                   []
% 3.94/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.94/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.94/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.94/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.94/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.94/1.00  --sup_full_bw                           [BwDemod]
% 3.94/1.00  --sup_immed_triv                        [TrivRules]
% 3.94/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.94/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.94/1.00  --sup_immed_bw_main                     []
% 3.94/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.94/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.94/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.94/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.94/1.00  
% 3.94/1.00  ------ Combination Options
% 3.94/1.00  
% 3.94/1.00  --comb_res_mult                         3
% 3.94/1.00  --comb_sup_mult                         2
% 3.94/1.00  --comb_inst_mult                        10
% 3.94/1.00  
% 3.94/1.00  ------ Debug Options
% 3.94/1.00  
% 3.94/1.00  --dbg_backtrace                         false
% 3.94/1.00  --dbg_dump_prop_clauses                 false
% 3.94/1.00  --dbg_dump_prop_clauses_file            -
% 3.94/1.00  --dbg_out_stat                          false
% 3.94/1.00  ------ Parsing...
% 3.94/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  ------ Proving...
% 3.94/1.00  ------ Problem Properties 
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  clauses                                 18
% 3.94/1.00  conjectures                             4
% 3.94/1.00  EPR                                     3
% 3.94/1.00  Horn                                    13
% 3.94/1.00  unary                                   6
% 3.94/1.00  binary                                  7
% 3.94/1.00  lits                                    36
% 3.94/1.00  lits eq                                 8
% 3.94/1.00  fd_pure                                 0
% 3.94/1.00  fd_pseudo                               0
% 3.94/1.00  fd_cond                                 0
% 3.94/1.00  fd_pseudo_cond                          3
% 3.94/1.00  AC symbols                              0
% 3.94/1.00  
% 3.94/1.00  ------ Schedule dynamic 5 is on 
% 3.94/1.00  
% 3.94/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ 
% 3.94/1.00  Current options:
% 3.94/1.00  ------ 
% 3.94/1.00  
% 3.94/1.00  ------ Input Options
% 3.94/1.00  
% 3.94/1.00  --out_options                           all
% 3.94/1.00  --tptp_safe_out                         true
% 3.94/1.00  --problem_path                          ""
% 3.94/1.00  --include_path                          ""
% 3.94/1.00  --clausifier                            res/vclausify_rel
% 3.94/1.00  --clausifier_options                    --mode clausify
% 3.94/1.00  --stdin                                 false
% 3.94/1.00  --stats_out                             all
% 3.94/1.00  
% 3.94/1.00  ------ General Options
% 3.94/1.00  
% 3.94/1.00  --fof                                   false
% 3.94/1.00  --time_out_real                         305.
% 3.94/1.00  --time_out_virtual                      -1.
% 3.94/1.00  --symbol_type_check                     false
% 3.94/1.00  --clausify_out                          false
% 3.94/1.00  --sig_cnt_out                           false
% 3.94/1.00  --trig_cnt_out                          false
% 3.94/1.00  --trig_cnt_out_tolerance                1.
% 3.94/1.00  --trig_cnt_out_sk_spl                   false
% 3.94/1.00  --abstr_cl_out                          false
% 3.94/1.00  
% 3.94/1.00  ------ Global Options
% 3.94/1.00  
% 3.94/1.00  --schedule                              default
% 3.94/1.00  --add_important_lit                     false
% 3.94/1.00  --prop_solver_per_cl                    1000
% 3.94/1.00  --min_unsat_core                        false
% 3.94/1.00  --soft_assumptions                      false
% 3.94/1.00  --soft_lemma_size                       3
% 3.94/1.00  --prop_impl_unit_size                   0
% 3.94/1.00  --prop_impl_unit                        []
% 3.94/1.00  --share_sel_clauses                     true
% 3.94/1.00  --reset_solvers                         false
% 3.94/1.00  --bc_imp_inh                            [conj_cone]
% 3.94/1.00  --conj_cone_tolerance                   3.
% 3.94/1.00  --extra_neg_conj                        none
% 3.94/1.00  --large_theory_mode                     true
% 3.94/1.00  --prolific_symb_bound                   200
% 3.94/1.00  --lt_threshold                          2000
% 3.94/1.00  --clause_weak_htbl                      true
% 3.94/1.00  --gc_record_bc_elim                     false
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing Options
% 3.94/1.00  
% 3.94/1.00  --preprocessing_flag                    true
% 3.94/1.00  --time_out_prep_mult                    0.1
% 3.94/1.00  --splitting_mode                        input
% 3.94/1.00  --splitting_grd                         true
% 3.94/1.00  --splitting_cvd                         false
% 3.94/1.00  --splitting_cvd_svl                     false
% 3.94/1.00  --splitting_nvd                         32
% 3.94/1.00  --sub_typing                            true
% 3.94/1.00  --prep_gs_sim                           true
% 3.94/1.00  --prep_unflatten                        true
% 3.94/1.00  --prep_res_sim                          true
% 3.94/1.00  --prep_upred                            true
% 3.94/1.00  --prep_sem_filter                       exhaustive
% 3.94/1.00  --prep_sem_filter_out                   false
% 3.94/1.00  --pred_elim                             true
% 3.94/1.00  --res_sim_input                         true
% 3.94/1.00  --eq_ax_congr_red                       true
% 3.94/1.00  --pure_diseq_elim                       true
% 3.94/1.00  --brand_transform                       false
% 3.94/1.00  --non_eq_to_eq                          false
% 3.94/1.00  --prep_def_merge                        true
% 3.94/1.00  --prep_def_merge_prop_impl              false
% 3.94/1.00  --prep_def_merge_mbd                    true
% 3.94/1.00  --prep_def_merge_tr_red                 false
% 3.94/1.00  --prep_def_merge_tr_cl                  false
% 3.94/1.00  --smt_preprocessing                     true
% 3.94/1.00  --smt_ac_axioms                         fast
% 3.94/1.00  --preprocessed_out                      false
% 3.94/1.00  --preprocessed_stats                    false
% 3.94/1.00  
% 3.94/1.00  ------ Abstraction refinement Options
% 3.94/1.00  
% 3.94/1.00  --abstr_ref                             []
% 3.94/1.00  --abstr_ref_prep                        false
% 3.94/1.00  --abstr_ref_until_sat                   false
% 3.94/1.00  --abstr_ref_sig_restrict                funpre
% 3.94/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.94/1.00  --abstr_ref_under                       []
% 3.94/1.00  
% 3.94/1.00  ------ SAT Options
% 3.94/1.00  
% 3.94/1.00  --sat_mode                              false
% 3.94/1.00  --sat_fm_restart_options                ""
% 3.94/1.00  --sat_gr_def                            false
% 3.94/1.00  --sat_epr_types                         true
% 3.94/1.00  --sat_non_cyclic_types                  false
% 3.94/1.00  --sat_finite_models                     false
% 3.94/1.00  --sat_fm_lemmas                         false
% 3.94/1.00  --sat_fm_prep                           false
% 3.94/1.00  --sat_fm_uc_incr                        true
% 3.94/1.00  --sat_out_model                         small
% 3.94/1.00  --sat_out_clauses                       false
% 3.94/1.00  
% 3.94/1.00  ------ QBF Options
% 3.94/1.00  
% 3.94/1.00  --qbf_mode                              false
% 3.94/1.00  --qbf_elim_univ                         false
% 3.94/1.00  --qbf_dom_inst                          none
% 3.94/1.00  --qbf_dom_pre_inst                      false
% 3.94/1.00  --qbf_sk_in                             false
% 3.94/1.00  --qbf_pred_elim                         true
% 3.94/1.00  --qbf_split                             512
% 3.94/1.00  
% 3.94/1.00  ------ BMC1 Options
% 3.94/1.00  
% 3.94/1.00  --bmc1_incremental                      false
% 3.94/1.00  --bmc1_axioms                           reachable_all
% 3.94/1.00  --bmc1_min_bound                        0
% 3.94/1.00  --bmc1_max_bound                        -1
% 3.94/1.00  --bmc1_max_bound_default                -1
% 3.94/1.00  --bmc1_symbol_reachability              true
% 3.94/1.00  --bmc1_property_lemmas                  false
% 3.94/1.00  --bmc1_k_induction                      false
% 3.94/1.00  --bmc1_non_equiv_states                 false
% 3.94/1.00  --bmc1_deadlock                         false
% 3.94/1.00  --bmc1_ucm                              false
% 3.94/1.00  --bmc1_add_unsat_core                   none
% 3.94/1.00  --bmc1_unsat_core_children              false
% 3.94/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.94/1.00  --bmc1_out_stat                         full
% 3.94/1.00  --bmc1_ground_init                      false
% 3.94/1.00  --bmc1_pre_inst_next_state              false
% 3.94/1.00  --bmc1_pre_inst_state                   false
% 3.94/1.00  --bmc1_pre_inst_reach_state             false
% 3.94/1.00  --bmc1_out_unsat_core                   false
% 3.94/1.00  --bmc1_aig_witness_out                  false
% 3.94/1.00  --bmc1_verbose                          false
% 3.94/1.00  --bmc1_dump_clauses_tptp                false
% 3.94/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.94/1.00  --bmc1_dump_file                        -
% 3.94/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.94/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.94/1.00  --bmc1_ucm_extend_mode                  1
% 3.94/1.00  --bmc1_ucm_init_mode                    2
% 3.94/1.00  --bmc1_ucm_cone_mode                    none
% 3.94/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.94/1.00  --bmc1_ucm_relax_model                  4
% 3.94/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.94/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.94/1.00  --bmc1_ucm_layered_model                none
% 3.94/1.00  --bmc1_ucm_max_lemma_size               10
% 3.94/1.00  
% 3.94/1.00  ------ AIG Options
% 3.94/1.00  
% 3.94/1.00  --aig_mode                              false
% 3.94/1.00  
% 3.94/1.00  ------ Instantiation Options
% 3.94/1.00  
% 3.94/1.00  --instantiation_flag                    true
% 3.94/1.00  --inst_sos_flag                         false
% 3.94/1.00  --inst_sos_phase                        true
% 3.94/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.94/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.94/1.00  --inst_lit_sel_side                     none
% 3.94/1.00  --inst_solver_per_active                1400
% 3.94/1.00  --inst_solver_calls_frac                1.
% 3.94/1.00  --inst_passive_queue_type               priority_queues
% 3.94/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.94/1.00  --inst_passive_queues_freq              [25;2]
% 3.94/1.00  --inst_dismatching                      true
% 3.94/1.00  --inst_eager_unprocessed_to_passive     true
% 3.94/1.00  --inst_prop_sim_given                   true
% 3.94/1.00  --inst_prop_sim_new                     false
% 3.94/1.00  --inst_subs_new                         false
% 3.94/1.00  --inst_eq_res_simp                      false
% 3.94/1.00  --inst_subs_given                       false
% 3.94/1.00  --inst_orphan_elimination               true
% 3.94/1.00  --inst_learning_loop_flag               true
% 3.94/1.00  --inst_learning_start                   3000
% 3.94/1.00  --inst_learning_factor                  2
% 3.94/1.00  --inst_start_prop_sim_after_learn       3
% 3.94/1.00  --inst_sel_renew                        solver
% 3.94/1.00  --inst_lit_activity_flag                true
% 3.94/1.00  --inst_restr_to_given                   false
% 3.94/1.00  --inst_activity_threshold               500
% 3.94/1.00  --inst_out_proof                        true
% 3.94/1.00  
% 3.94/1.00  ------ Resolution Options
% 3.94/1.00  
% 3.94/1.00  --resolution_flag                       false
% 3.94/1.00  --res_lit_sel                           adaptive
% 3.94/1.00  --res_lit_sel_side                      none
% 3.94/1.00  --res_ordering                          kbo
% 3.94/1.00  --res_to_prop_solver                    active
% 3.94/1.00  --res_prop_simpl_new                    false
% 3.94/1.00  --res_prop_simpl_given                  true
% 3.94/1.00  --res_passive_queue_type                priority_queues
% 3.94/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.94/1.00  --res_passive_queues_freq               [15;5]
% 3.94/1.00  --res_forward_subs                      full
% 3.94/1.00  --res_backward_subs                     full
% 3.94/1.00  --res_forward_subs_resolution           true
% 3.94/1.00  --res_backward_subs_resolution          true
% 3.94/1.00  --res_orphan_elimination                true
% 3.94/1.00  --res_time_limit                        2.
% 3.94/1.00  --res_out_proof                         true
% 3.94/1.00  
% 3.94/1.00  ------ Superposition Options
% 3.94/1.00  
% 3.94/1.00  --superposition_flag                    true
% 3.94/1.00  --sup_passive_queue_type                priority_queues
% 3.94/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.94/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.94/1.00  --demod_completeness_check              fast
% 3.94/1.00  --demod_use_ground                      true
% 3.94/1.00  --sup_to_prop_solver                    passive
% 3.94/1.00  --sup_prop_simpl_new                    true
% 3.94/1.00  --sup_prop_simpl_given                  true
% 3.94/1.00  --sup_fun_splitting                     false
% 3.94/1.00  --sup_smt_interval                      50000
% 3.94/1.00  
% 3.94/1.00  ------ Superposition Simplification Setup
% 3.94/1.00  
% 3.94/1.00  --sup_indices_passive                   []
% 3.94/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.94/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.94/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.94/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.94/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.94/1.00  --sup_full_bw                           [BwDemod]
% 3.94/1.00  --sup_immed_triv                        [TrivRules]
% 3.94/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.94/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.94/1.00  --sup_immed_bw_main                     []
% 3.94/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.94/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.94/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.94/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.94/1.00  
% 3.94/1.00  ------ Combination Options
% 3.94/1.00  
% 3.94/1.00  --comb_res_mult                         3
% 3.94/1.00  --comb_sup_mult                         2
% 3.94/1.00  --comb_inst_mult                        10
% 3.94/1.00  
% 3.94/1.00  ------ Debug Options
% 3.94/1.00  
% 3.94/1.00  --dbg_backtrace                         false
% 3.94/1.00  --dbg_dump_prop_clauses                 false
% 3.94/1.00  --dbg_dump_prop_clauses_file            -
% 3.94/1.00  --dbg_out_stat                          false
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  % SZS status Theorem for theBenchmark.p
% 3.94/1.00  
% 3.94/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.94/1.00  
% 3.94/1.00  fof(f11,conjecture,(
% 3.94/1.00    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 3.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/1.00  
% 3.94/1.00  fof(f12,negated_conjecture,(
% 3.94/1.00    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 3.94/1.00    inference(negated_conjecture,[],[f11])).
% 3.94/1.00  
% 3.94/1.00  fof(f15,plain,(
% 3.94/1.00    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 3.94/1.00    inference(ennf_transformation,[],[f12])).
% 3.94/1.00  
% 3.94/1.00  fof(f16,plain,(
% 3.94/1.00    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 3.94/1.00    inference(flattening,[],[f15])).
% 3.94/1.00  
% 3.94/1.00  fof(f27,plain,(
% 3.94/1.00    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k3_xboole_0(sK2,sK4) != k1_tarski(sK5) & r2_hidden(sK5,sK2) & k3_xboole_0(sK3,sK4) = k1_tarski(sK5) & r1_tarski(sK2,sK3))),
% 3.94/1.00    introduced(choice_axiom,[])).
% 3.94/1.00  
% 3.94/1.00  fof(f28,plain,(
% 3.94/1.00    k3_xboole_0(sK2,sK4) != k1_tarski(sK5) & r2_hidden(sK5,sK2) & k3_xboole_0(sK3,sK4) = k1_tarski(sK5) & r1_tarski(sK2,sK3)),
% 3.94/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f16,f27])).
% 3.94/1.00  
% 3.94/1.00  fof(f49,plain,(
% 3.94/1.00    r2_hidden(sK5,sK2)),
% 3.94/1.00    inference(cnf_transformation,[],[f28])).
% 3.94/1.00  
% 3.94/1.00  fof(f1,axiom,(
% 3.94/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/1.00  
% 3.94/1.00  fof(f29,plain,(
% 3.94/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.94/1.00    inference(cnf_transformation,[],[f1])).
% 3.94/1.00  
% 3.94/1.00  fof(f6,axiom,(
% 3.94/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/1.00  
% 3.94/1.00  fof(f41,plain,(
% 3.94/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.94/1.00    inference(cnf_transformation,[],[f6])).
% 3.94/1.00  
% 3.94/1.00  fof(f53,plain,(
% 3.94/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.94/1.00    inference(definition_unfolding,[],[f29,f41,f41])).
% 3.94/1.00  
% 3.94/1.00  fof(f48,plain,(
% 3.94/1.00    k3_xboole_0(sK3,sK4) = k1_tarski(sK5)),
% 3.94/1.00    inference(cnf_transformation,[],[f28])).
% 3.94/1.00  
% 3.94/1.00  fof(f7,axiom,(
% 3.94/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/1.00  
% 3.94/1.00  fof(f42,plain,(
% 3.94/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.94/1.00    inference(cnf_transformation,[],[f7])).
% 3.94/1.00  
% 3.94/1.00  fof(f8,axiom,(
% 3.94/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/1.00  
% 3.94/1.00  fof(f43,plain,(
% 3.94/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.94/1.00    inference(cnf_transformation,[],[f8])).
% 3.94/1.00  
% 3.94/1.00  fof(f9,axiom,(
% 3.94/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/1.00  
% 3.94/1.00  fof(f44,plain,(
% 3.94/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.94/1.00    inference(cnf_transformation,[],[f9])).
% 3.94/1.00  
% 3.94/1.00  fof(f51,plain,(
% 3.94/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.94/1.00    inference(definition_unfolding,[],[f43,f44])).
% 3.94/1.00  
% 3.94/1.00  fof(f52,plain,(
% 3.94/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.94/1.00    inference(definition_unfolding,[],[f42,f51])).
% 3.94/1.00  
% 3.94/1.00  fof(f59,plain,(
% 3.94/1.00    k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k2_enumset1(sK5,sK5,sK5,sK5)),
% 3.94/1.00    inference(definition_unfolding,[],[f48,f41,f52])).
% 3.94/1.00  
% 3.94/1.00  fof(f10,axiom,(
% 3.94/1.00    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/1.00  
% 3.94/1.00  fof(f26,plain,(
% 3.94/1.00    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 3.94/1.00    inference(nnf_transformation,[],[f10])).
% 3.94/1.00  
% 3.94/1.00  fof(f46,plain,(
% 3.94/1.00    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.94/1.00    inference(cnf_transformation,[],[f26])).
% 3.94/1.00  
% 3.94/1.00  fof(f56,plain,(
% 3.94/1.00    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.94/1.00    inference(definition_unfolding,[],[f46,f52])).
% 3.94/1.00  
% 3.94/1.00  fof(f5,axiom,(
% 3.94/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/1.00  
% 3.94/1.00  fof(f14,plain,(
% 3.94/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.94/1.00    inference(ennf_transformation,[],[f5])).
% 3.94/1.00  
% 3.94/1.00  fof(f40,plain,(
% 3.94/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.94/1.00    inference(cnf_transformation,[],[f14])).
% 3.94/1.00  
% 3.94/1.00  fof(f55,plain,(
% 3.94/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.94/1.00    inference(definition_unfolding,[],[f40,f41])).
% 3.94/1.00  
% 3.94/1.00  fof(f4,axiom,(
% 3.94/1.00    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.94/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/1.00  
% 3.94/1.00  fof(f39,plain,(
% 3.94/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.94/1.00    inference(cnf_transformation,[],[f4])).
% 3.94/1.00  
% 3.94/1.00  fof(f54,plain,(
% 3.94/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) )),
% 3.94/1.00    inference(definition_unfolding,[],[f39,f41,f41,f41,f41])).
% 3.94/1.00  
% 3.94/1.00  fof(f47,plain,(
% 3.94/1.00    r1_tarski(sK2,sK3)),
% 3.94/1.00    inference(cnf_transformation,[],[f28])).
% 3.94/1.00  
% 3.94/1.00  fof(f50,plain,(
% 3.94/1.00    k3_xboole_0(sK2,sK4) != k1_tarski(sK5)),
% 3.94/1.00    inference(cnf_transformation,[],[f28])).
% 3.94/1.00  
% 3.94/1.00  fof(f58,plain,(
% 3.94/1.00    k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k2_enumset1(sK5,sK5,sK5,sK5)),
% 3.94/1.00    inference(definition_unfolding,[],[f50,f41,f52])).
% 3.94/1.00  
% 3.94/1.00  cnf(c_15,negated_conjecture,
% 3.94/1.00      ( r2_hidden(sK5,sK2) ),
% 3.94/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_689,plain,
% 3.94/1.00      ( r2_hidden(sK5,sK2) = iProver_top ),
% 3.94/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_0,plain,
% 3.94/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.94/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_16,negated_conjecture,
% 3.94/1.00      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK4)) = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 3.94/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_709,plain,
% 3.94/1.00      ( k2_enumset1(sK5,sK5,sK5,sK5) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) ),
% 3.94/1.00      inference(demodulation,[status(thm)],[c_0,c_16]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_12,plain,
% 3.94/1.00      ( ~ r2_hidden(X0,X1) | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ),
% 3.94/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_691,plain,
% 3.94/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.94/1.00      | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top ),
% 3.94/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_2000,plain,
% 3.94/1.00      ( r2_hidden(sK5,X0) != iProver_top
% 3.94/1.00      | r1_tarski(k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)),X0) = iProver_top ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_709,c_691]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_11,plain,
% 3.94/1.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 3.94/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_692,plain,
% 3.94/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 3.94/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.94/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_3334,plain,
% 3.94/1.00      ( k4_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)),k4_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)),X0)) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK3))
% 3.94/1.00      | r2_hidden(sK5,X0) != iProver_top ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_2000,c_692]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_10,plain,
% 3.94/1.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 3.94/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_3338,plain,
% 3.94/1.00      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK3))
% 3.94/1.00      | r2_hidden(sK5,X0) != iProver_top ),
% 3.94/1.00      inference(demodulation,[status(thm)],[c_3334,c_10]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_15468,plain,
% 3.94/1.00      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)))) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_689,c_3338]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_17,negated_conjecture,
% 3.94/1.00      ( r1_tarski(sK2,sK3) ),
% 3.94/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_688,plain,
% 3.94/1.00      ( r1_tarski(sK2,sK3) = iProver_top ),
% 3.94/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_877,plain,
% 3.94/1.00      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = sK2 ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_688,c_692]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_1096,plain,
% 3.94/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_0,c_10]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_2709,plain,
% 3.94/1.00      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,sK2)) ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_877,c_1096]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_1112,plain,
% 3.94/1.00      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_877,c_10]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_1474,plain,
% 3.94/1.00      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,sK3)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_0,c_1112]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_3783,plain,
% 3.94/1.00      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_2709,c_1474]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_3844,plain,
% 3.94/1.00      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) = sK2 ),
% 3.94/1.00      inference(light_normalisation,[status(thm)],[c_3783,c_877]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_15483,plain,
% 3.94/1.00      ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) ),
% 3.94/1.00      inference(light_normalisation,[status(thm)],[c_15468,c_3844]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_16738,plain,
% 3.94/1.00      ( k2_enumset1(sK5,sK5,sK5,sK5) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) ),
% 3.94/1.00      inference(demodulation,[status(thm)],[c_15483,c_709]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_1830,plain,
% 3.94/1.00      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) ),
% 3.94/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_348,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_1079,plain,
% 3.94/1.00      ( k2_enumset1(X0,X1,X2,X3) != X4
% 3.94/1.00      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != X4
% 3.94/1.00      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k2_enumset1(X0,X1,X2,X3) ),
% 3.94/1.00      inference(instantiation,[status(thm)],[c_348]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_1829,plain,
% 3.94/1.00      ( k2_enumset1(X0,X1,X2,X3) != k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))
% 3.94/1.00      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k2_enumset1(X0,X1,X2,X3)
% 3.94/1.00      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) ),
% 3.94/1.00      inference(instantiation,[status(thm)],[c_1079]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_1831,plain,
% 3.94/1.00      ( k2_enumset1(sK5,sK5,sK5,sK5) != k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))
% 3.94/1.00      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k2_enumset1(sK5,sK5,sK5,sK5)
% 3.94/1.00      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) ),
% 3.94/1.00      inference(instantiation,[status(thm)],[c_1829]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_14,negated_conjecture,
% 3.94/1.00      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k2_enumset1(sK5,sK5,sK5,sK5) ),
% 3.94/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(contradiction,plain,
% 3.94/1.00      ( $false ),
% 3.94/1.00      inference(minisat,[status(thm)],[c_16738,c_1830,c_1831,c_14]) ).
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.94/1.00  
% 3.94/1.00  ------                               Statistics
% 3.94/1.00  
% 3.94/1.00  ------ General
% 3.94/1.00  
% 3.94/1.00  abstr_ref_over_cycles:                  0
% 3.94/1.00  abstr_ref_under_cycles:                 0
% 3.94/1.00  gc_basic_clause_elim:                   0
% 3.94/1.00  forced_gc_time:                         0
% 3.94/1.00  parsing_time:                           0.007
% 3.94/1.00  unif_index_cands_time:                  0.
% 3.94/1.00  unif_index_add_time:                    0.
% 3.94/1.00  orderings_time:                         0.
% 3.94/1.00  out_proof_time:                         0.007
% 3.94/1.00  total_time:                             0.498
% 3.94/1.00  num_of_symbols:                         41
% 3.94/1.00  num_of_terms:                           25134
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing
% 3.94/1.00  
% 3.94/1.00  num_of_splits:                          0
% 3.94/1.00  num_of_split_atoms:                     0
% 3.94/1.00  num_of_reused_defs:                     0
% 3.94/1.00  num_eq_ax_congr_red:                    10
% 3.94/1.00  num_of_sem_filtered_clauses:            1
% 3.94/1.00  num_of_subtypes:                        0
% 3.94/1.00  monotx_restored_types:                  0
% 3.94/1.00  sat_num_of_epr_types:                   0
% 3.94/1.00  sat_num_of_non_cyclic_types:            0
% 3.94/1.00  sat_guarded_non_collapsed_types:        0
% 3.94/1.00  num_pure_diseq_elim:                    0
% 3.94/1.00  simp_replaced_by:                       0
% 3.94/1.00  res_preprocessed:                       67
% 3.94/1.00  prep_upred:                             0
% 3.94/1.00  prep_unflattend:                        17
% 3.94/1.00  smt_new_axioms:                         0
% 3.94/1.00  pred_elim_cands:                        2
% 3.94/1.00  pred_elim:                              0
% 3.94/1.00  pred_elim_cl:                           0
% 3.94/1.00  pred_elim_cycles:                       1
% 3.94/1.00  merged_defs:                            6
% 3.94/1.00  merged_defs_ncl:                        0
% 3.94/1.00  bin_hyper_res:                          6
% 3.94/1.00  prep_cycles:                            3
% 3.94/1.00  pred_elim_time:                         0.002
% 3.94/1.00  splitting_time:                         0.
% 3.94/1.00  sem_filter_time:                        0.
% 3.94/1.00  monotx_time:                            0.
% 3.94/1.00  subtype_inf_time:                       0.
% 3.94/1.00  
% 3.94/1.00  ------ Problem properties
% 3.94/1.00  
% 3.94/1.00  clauses:                                18
% 3.94/1.00  conjectures:                            4
% 3.94/1.00  epr:                                    3
% 3.94/1.00  horn:                                   13
% 3.94/1.00  ground:                                 4
% 3.94/1.00  unary:                                  6
% 3.94/1.00  binary:                                 7
% 3.94/1.00  lits:                                   36
% 3.94/1.00  lits_eq:                                8
% 3.94/1.00  fd_pure:                                0
% 3.94/1.00  fd_pseudo:                              0
% 3.94/1.00  fd_cond:                                0
% 3.94/1.00  fd_pseudo_cond:                         3
% 3.94/1.00  ac_symbols:                             0
% 3.94/1.00  
% 3.94/1.00  ------ Propositional Solver
% 3.94/1.00  
% 3.94/1.00  prop_solver_calls:                      25
% 3.94/1.00  prop_fast_solver_calls:                 460
% 3.94/1.00  smt_solver_calls:                       0
% 3.94/1.00  smt_fast_solver_calls:                  0
% 3.94/1.00  prop_num_of_clauses:                    5900
% 3.94/1.00  prop_preprocess_simplified:             8980
% 3.94/1.00  prop_fo_subsumed:                       4
% 3.94/1.00  prop_solver_time:                       0.
% 3.94/1.00  smt_solver_time:                        0.
% 3.94/1.00  smt_fast_solver_time:                   0.
% 3.94/1.00  prop_fast_solver_time:                  0.
% 3.94/1.00  prop_unsat_core_time:                   0.
% 3.94/1.00  
% 3.94/1.00  ------ QBF
% 3.94/1.00  
% 3.94/1.00  qbf_q_res:                              0
% 3.94/1.00  qbf_num_tautologies:                    0
% 3.94/1.00  qbf_prep_cycles:                        0
% 3.94/1.00  
% 3.94/1.00  ------ BMC1
% 3.94/1.00  
% 3.94/1.00  bmc1_current_bound:                     -1
% 3.94/1.00  bmc1_last_solved_bound:                 -1
% 3.94/1.00  bmc1_unsat_core_size:                   -1
% 3.94/1.00  bmc1_unsat_core_parents_size:           -1
% 3.94/1.00  bmc1_merge_next_fun:                    0
% 3.94/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.94/1.00  
% 3.94/1.00  ------ Instantiation
% 3.94/1.00  
% 3.94/1.00  inst_num_of_clauses:                    1009
% 3.94/1.00  inst_num_in_passive:                    516
% 3.94/1.00  inst_num_in_active:                     346
% 3.94/1.00  inst_num_in_unprocessed:                147
% 3.94/1.00  inst_num_of_loops:                      410
% 3.94/1.00  inst_num_of_learning_restarts:          0
% 3.94/1.00  inst_num_moves_active_passive:          62
% 3.94/1.00  inst_lit_activity:                      0
% 3.94/1.00  inst_lit_activity_moves:                0
% 3.94/1.00  inst_num_tautologies:                   0
% 3.94/1.00  inst_num_prop_implied:                  0
% 3.94/1.00  inst_num_existing_simplified:           0
% 3.94/1.00  inst_num_eq_res_simplified:             0
% 3.94/1.00  inst_num_child_elim:                    0
% 3.94/1.00  inst_num_of_dismatching_blockings:      1006
% 3.94/1.00  inst_num_of_non_proper_insts:           1055
% 3.94/1.00  inst_num_of_duplicates:                 0
% 3.94/1.00  inst_inst_num_from_inst_to_res:         0
% 3.94/1.00  inst_dismatching_checking_time:         0.
% 3.94/1.00  
% 3.94/1.00  ------ Resolution
% 3.94/1.00  
% 3.94/1.00  res_num_of_clauses:                     0
% 3.94/1.00  res_num_in_passive:                     0
% 3.94/1.00  res_num_in_active:                      0
% 3.94/1.00  res_num_of_loops:                       70
% 3.94/1.00  res_forward_subset_subsumed:            42
% 3.94/1.00  res_backward_subset_subsumed:           0
% 3.94/1.00  res_forward_subsumed:                   0
% 3.94/1.00  res_backward_subsumed:                  0
% 3.94/1.00  res_forward_subsumption_resolution:     0
% 3.94/1.00  res_backward_subsumption_resolution:    0
% 3.94/1.00  res_clause_to_clause_subsumption:       10006
% 3.94/1.00  res_orphan_elimination:                 0
% 3.94/1.00  res_tautology_del:                      110
% 3.94/1.00  res_num_eq_res_simplified:              0
% 3.94/1.00  res_num_sel_changes:                    0
% 3.94/1.00  res_moves_from_active_to_pass:          0
% 3.94/1.00  
% 3.94/1.00  ------ Superposition
% 3.94/1.00  
% 3.94/1.00  sup_time_total:                         0.
% 3.94/1.00  sup_time_generating:                    0.
% 3.94/1.00  sup_time_sim_full:                      0.
% 3.94/1.00  sup_time_sim_immed:                     0.
% 3.94/1.00  
% 3.94/1.00  sup_num_of_clauses:                     990
% 3.94/1.00  sup_num_in_active:                      76
% 3.94/1.00  sup_num_in_passive:                     914
% 3.94/1.00  sup_num_of_loops:                       81
% 3.94/1.00  sup_fw_superposition:                   1714
% 3.94/1.00  sup_bw_superposition:                   1110
% 3.94/1.00  sup_immediate_simplified:               631
% 3.94/1.00  sup_given_eliminated:                   1
% 3.94/1.00  comparisons_done:                       0
% 3.94/1.00  comparisons_avoided:                    0
% 3.94/1.00  
% 3.94/1.00  ------ Simplifications
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  sim_fw_subset_subsumed:                 22
% 3.94/1.00  sim_bw_subset_subsumed:                 17
% 3.94/1.00  sim_fw_subsumed:                        154
% 3.94/1.00  sim_bw_subsumed:                        22
% 3.94/1.00  sim_fw_subsumption_res:                 2
% 3.94/1.00  sim_bw_subsumption_res:                 0
% 3.94/1.00  sim_tautology_del:                      33
% 3.94/1.00  sim_eq_tautology_del:                   32
% 3.94/1.00  sim_eq_res_simp:                        1
% 3.94/1.00  sim_fw_demodulated:                     284
% 3.94/1.00  sim_bw_demodulated:                     30
% 3.94/1.00  sim_light_normalised:                   231
% 3.94/1.00  sim_joinable_taut:                      0
% 3.94/1.00  sim_joinable_simp:                      0
% 3.94/1.00  sim_ac_normalised:                      0
% 3.94/1.00  sim_smt_subsumption:                    0
% 3.94/1.00  
%------------------------------------------------------------------------------
