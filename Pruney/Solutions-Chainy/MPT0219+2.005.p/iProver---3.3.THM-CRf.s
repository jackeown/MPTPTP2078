%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:10 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 127 expanded)
%              Number of clauses        :   26 (  29 expanded)
%              Number of leaves         :   13 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  163 ( 348 expanded)
%              Number of equality atoms :   83 ( 208 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f22])).

fof(f27,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f48,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK4 != sK5
      & k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( sK4 != sK5
    & k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f27,f48])).

fof(f90,plain,(
    k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f92,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f68,f64])).

fof(f17,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f122,plain,(
    k5_xboole_0(k2_tarski(sK4,sK4),k5_xboole_0(k2_tarski(sK5,sK5),k3_xboole_0(k2_tarski(sK5,sK5),k2_tarski(sK4,sK4)))) = k2_tarski(sK4,sK4) ),
    inference(definition_unfolding,[],[f90,f92,f85,f85,f85])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f99,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f50,f92,f92])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f107,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f67,f92])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f45,f46])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f118,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f78,f85])).

fof(f135,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f118])).

fof(f136,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f135])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f119,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f77,f85])).

fof(f137,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_tarski(X0,X0)) ) ),
    inference(equality_resolution,[],[f119])).

fof(f91,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1928,plain,
    ( ~ r2_hidden(sK5,X0)
    | r2_hidden(sK5,k2_tarski(X1,X1))
    | ~ r1_tarski(X0,k2_tarski(X1,X1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3972,plain,
    ( r2_hidden(sK5,k2_tarski(X0,X0))
    | ~ r2_hidden(sK5,k2_tarski(sK5,sK5))
    | ~ r1_tarski(k2_tarski(sK5,sK5),k2_tarski(X0,X0)) ),
    inference(instantiation,[status(thm)],[c_1928])).

cnf(c_3974,plain,
    ( ~ r2_hidden(sK5,k2_tarski(sK5,sK5))
    | r2_hidden(sK5,k2_tarski(sK4,sK4))
    | ~ r1_tarski(k2_tarski(sK5,sK5),k2_tarski(sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_3972])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_34,negated_conjecture,
    ( k5_xboole_0(k2_tarski(sK4,sK4),k5_xboole_0(k2_tarski(sK5,sK5),k3_xboole_0(k2_tarski(sK5,sK5),k2_tarski(sK4,sK4)))) = k2_tarski(sK4,sK4) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_1124,plain,
    ( k5_xboole_0(k2_tarski(sK4,sK4),k5_xboole_0(k2_tarski(sK5,sK5),k3_xboole_0(k2_tarski(sK4,sK4),k2_tarski(sK5,sK5)))) = k2_tarski(sK4,sK4) ),
    inference(demodulation,[status(thm)],[c_3,c_34])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_18,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_868,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2194,plain,
    ( r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_868])).

cnf(c_2332,plain,
    ( r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_2194])).

cnf(c_2654,plain,
    ( r1_tarski(k2_tarski(sK5,sK5),k2_tarski(sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1124,c_2332])).

cnf(c_2661,plain,
    ( r1_tarski(k2_tarski(sK5,sK5),k2_tarski(sK4,sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2654])).

cnf(c_29,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_1400,plain,
    ( r2_hidden(sK5,k2_tarski(sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_30,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f137])).

cnf(c_1197,plain,
    ( ~ r2_hidden(sK5,k2_tarski(X0,X0))
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_1199,plain,
    ( ~ r2_hidden(sK5,k2_tarski(sK4,sK4))
    | sK5 = sK4 ),
    inference(instantiation,[status(thm)],[c_1197])).

cnf(c_456,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1109,plain,
    ( sK5 != X0
    | sK4 != X0
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_456])).

cnf(c_1110,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1109])).

cnf(c_41,plain,
    ( r2_hidden(sK4,k2_tarski(sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_38,plain,
    ( ~ r2_hidden(sK4,k2_tarski(sK4,sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_33,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f91])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3974,c_2661,c_1400,c_1199,c_1110,c_41,c_38,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:01:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 1.69/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.01  
% 1.69/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.69/1.01  
% 1.69/1.01  ------  iProver source info
% 1.69/1.01  
% 1.69/1.01  git: date: 2020-06-30 10:37:57 +0100
% 1.69/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.69/1.01  git: non_committed_changes: false
% 1.69/1.01  git: last_make_outside_of_git: false
% 1.69/1.01  
% 1.69/1.01  ------ 
% 1.69/1.01  
% 1.69/1.01  ------ Input Options
% 1.69/1.01  
% 1.69/1.01  --out_options                           all
% 1.69/1.01  --tptp_safe_out                         true
% 1.69/1.01  --problem_path                          ""
% 1.69/1.01  --include_path                          ""
% 1.69/1.01  --clausifier                            res/vclausify_rel
% 1.69/1.01  --clausifier_options                    --mode clausify
% 1.69/1.01  --stdin                                 false
% 1.69/1.01  --stats_out                             all
% 1.69/1.01  
% 1.69/1.01  ------ General Options
% 1.69/1.01  
% 1.69/1.01  --fof                                   false
% 1.69/1.01  --time_out_real                         305.
% 1.69/1.01  --time_out_virtual                      -1.
% 1.69/1.01  --symbol_type_check                     false
% 1.69/1.01  --clausify_out                          false
% 1.69/1.01  --sig_cnt_out                           false
% 1.69/1.01  --trig_cnt_out                          false
% 1.69/1.01  --trig_cnt_out_tolerance                1.
% 1.69/1.01  --trig_cnt_out_sk_spl                   false
% 1.69/1.01  --abstr_cl_out                          false
% 1.69/1.01  
% 1.69/1.01  ------ Global Options
% 1.69/1.01  
% 1.69/1.01  --schedule                              default
% 1.69/1.01  --add_important_lit                     false
% 1.69/1.01  --prop_solver_per_cl                    1000
% 1.69/1.01  --min_unsat_core                        false
% 1.69/1.01  --soft_assumptions                      false
% 1.69/1.01  --soft_lemma_size                       3
% 1.69/1.01  --prop_impl_unit_size                   0
% 1.69/1.01  --prop_impl_unit                        []
% 1.69/1.01  --share_sel_clauses                     true
% 1.69/1.01  --reset_solvers                         false
% 1.69/1.01  --bc_imp_inh                            [conj_cone]
% 1.69/1.01  --conj_cone_tolerance                   3.
% 1.69/1.01  --extra_neg_conj                        none
% 1.69/1.01  --large_theory_mode                     true
% 1.69/1.01  --prolific_symb_bound                   200
% 1.69/1.01  --lt_threshold                          2000
% 1.69/1.01  --clause_weak_htbl                      true
% 1.69/1.01  --gc_record_bc_elim                     false
% 1.69/1.01  
% 1.69/1.01  ------ Preprocessing Options
% 1.69/1.01  
% 1.69/1.01  --preprocessing_flag                    true
% 1.69/1.01  --time_out_prep_mult                    0.1
% 1.69/1.01  --splitting_mode                        input
% 1.69/1.01  --splitting_grd                         true
% 1.69/1.01  --splitting_cvd                         false
% 1.69/1.01  --splitting_cvd_svl                     false
% 1.69/1.01  --splitting_nvd                         32
% 1.69/1.01  --sub_typing                            true
% 1.69/1.01  --prep_gs_sim                           true
% 1.69/1.01  --prep_unflatten                        true
% 1.69/1.01  --prep_res_sim                          true
% 1.69/1.01  --prep_upred                            true
% 1.69/1.01  --prep_sem_filter                       exhaustive
% 1.69/1.01  --prep_sem_filter_out                   false
% 1.69/1.01  --pred_elim                             true
% 1.69/1.01  --res_sim_input                         true
% 1.69/1.01  --eq_ax_congr_red                       true
% 1.69/1.01  --pure_diseq_elim                       true
% 1.69/1.01  --brand_transform                       false
% 1.69/1.01  --non_eq_to_eq                          false
% 1.69/1.01  --prep_def_merge                        true
% 1.69/1.01  --prep_def_merge_prop_impl              false
% 1.69/1.01  --prep_def_merge_mbd                    true
% 1.69/1.01  --prep_def_merge_tr_red                 false
% 1.69/1.01  --prep_def_merge_tr_cl                  false
% 1.69/1.01  --smt_preprocessing                     true
% 1.69/1.01  --smt_ac_axioms                         fast
% 1.69/1.01  --preprocessed_out                      false
% 1.69/1.01  --preprocessed_stats                    false
% 1.69/1.01  
% 1.69/1.01  ------ Abstraction refinement Options
% 1.69/1.01  
% 1.69/1.01  --abstr_ref                             []
% 1.69/1.01  --abstr_ref_prep                        false
% 1.69/1.01  --abstr_ref_until_sat                   false
% 1.69/1.01  --abstr_ref_sig_restrict                funpre
% 1.69/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.69/1.01  --abstr_ref_under                       []
% 1.69/1.01  
% 1.69/1.01  ------ SAT Options
% 1.69/1.01  
% 1.69/1.01  --sat_mode                              false
% 1.69/1.01  --sat_fm_restart_options                ""
% 1.69/1.01  --sat_gr_def                            false
% 1.69/1.01  --sat_epr_types                         true
% 1.69/1.01  --sat_non_cyclic_types                  false
% 1.69/1.01  --sat_finite_models                     false
% 1.69/1.01  --sat_fm_lemmas                         false
% 1.69/1.01  --sat_fm_prep                           false
% 1.69/1.01  --sat_fm_uc_incr                        true
% 1.69/1.01  --sat_out_model                         small
% 1.69/1.01  --sat_out_clauses                       false
% 1.69/1.01  
% 1.69/1.01  ------ QBF Options
% 1.69/1.01  
% 1.69/1.01  --qbf_mode                              false
% 1.69/1.01  --qbf_elim_univ                         false
% 1.69/1.01  --qbf_dom_inst                          none
% 1.69/1.01  --qbf_dom_pre_inst                      false
% 1.69/1.01  --qbf_sk_in                             false
% 1.69/1.01  --qbf_pred_elim                         true
% 1.69/1.01  --qbf_split                             512
% 1.69/1.01  
% 1.69/1.01  ------ BMC1 Options
% 1.69/1.01  
% 1.69/1.01  --bmc1_incremental                      false
% 1.69/1.01  --bmc1_axioms                           reachable_all
% 1.69/1.01  --bmc1_min_bound                        0
% 1.69/1.01  --bmc1_max_bound                        -1
% 1.69/1.01  --bmc1_max_bound_default                -1
% 1.69/1.01  --bmc1_symbol_reachability              true
% 1.69/1.01  --bmc1_property_lemmas                  false
% 1.69/1.01  --bmc1_k_induction                      false
% 1.69/1.01  --bmc1_non_equiv_states                 false
% 1.69/1.01  --bmc1_deadlock                         false
% 1.69/1.01  --bmc1_ucm                              false
% 1.69/1.01  --bmc1_add_unsat_core                   none
% 1.69/1.01  --bmc1_unsat_core_children              false
% 1.69/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.69/1.01  --bmc1_out_stat                         full
% 1.69/1.01  --bmc1_ground_init                      false
% 1.69/1.01  --bmc1_pre_inst_next_state              false
% 1.69/1.01  --bmc1_pre_inst_state                   false
% 1.69/1.01  --bmc1_pre_inst_reach_state             false
% 1.69/1.01  --bmc1_out_unsat_core                   false
% 1.69/1.01  --bmc1_aig_witness_out                  false
% 1.69/1.01  --bmc1_verbose                          false
% 1.69/1.01  --bmc1_dump_clauses_tptp                false
% 1.69/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.69/1.01  --bmc1_dump_file                        -
% 1.69/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.69/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.69/1.01  --bmc1_ucm_extend_mode                  1
% 1.69/1.01  --bmc1_ucm_init_mode                    2
% 1.69/1.01  --bmc1_ucm_cone_mode                    none
% 1.69/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.69/1.01  --bmc1_ucm_relax_model                  4
% 1.69/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.69/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.69/1.01  --bmc1_ucm_layered_model                none
% 1.69/1.01  --bmc1_ucm_max_lemma_size               10
% 1.69/1.01  
% 1.69/1.01  ------ AIG Options
% 1.69/1.01  
% 1.69/1.01  --aig_mode                              false
% 1.69/1.01  
% 1.69/1.01  ------ Instantiation Options
% 1.69/1.01  
% 1.69/1.01  --instantiation_flag                    true
% 1.69/1.01  --inst_sos_flag                         false
% 1.69/1.01  --inst_sos_phase                        true
% 1.69/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.69/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.69/1.01  --inst_lit_sel_side                     num_symb
% 1.69/1.01  --inst_solver_per_active                1400
% 1.69/1.01  --inst_solver_calls_frac                1.
% 1.69/1.01  --inst_passive_queue_type               priority_queues
% 1.69/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.69/1.01  --inst_passive_queues_freq              [25;2]
% 1.69/1.01  --inst_dismatching                      true
% 1.69/1.01  --inst_eager_unprocessed_to_passive     true
% 1.69/1.01  --inst_prop_sim_given                   true
% 1.69/1.01  --inst_prop_sim_new                     false
% 1.69/1.01  --inst_subs_new                         false
% 1.69/1.01  --inst_eq_res_simp                      false
% 1.69/1.01  --inst_subs_given                       false
% 1.69/1.01  --inst_orphan_elimination               true
% 1.69/1.01  --inst_learning_loop_flag               true
% 1.69/1.01  --inst_learning_start                   3000
% 1.69/1.01  --inst_learning_factor                  2
% 1.69/1.01  --inst_start_prop_sim_after_learn       3
% 1.69/1.01  --inst_sel_renew                        solver
% 1.69/1.01  --inst_lit_activity_flag                true
% 1.69/1.01  --inst_restr_to_given                   false
% 1.69/1.01  --inst_activity_threshold               500
% 1.69/1.01  --inst_out_proof                        true
% 1.69/1.01  
% 1.69/1.01  ------ Resolution Options
% 1.69/1.01  
% 1.69/1.01  --resolution_flag                       true
% 1.69/1.01  --res_lit_sel                           adaptive
% 1.69/1.01  --res_lit_sel_side                      none
% 1.69/1.01  --res_ordering                          kbo
% 1.69/1.01  --res_to_prop_solver                    active
% 1.69/1.01  --res_prop_simpl_new                    false
% 1.69/1.01  --res_prop_simpl_given                  true
% 1.69/1.01  --res_passive_queue_type                priority_queues
% 1.69/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.69/1.01  --res_passive_queues_freq               [15;5]
% 1.69/1.01  --res_forward_subs                      full
% 1.69/1.01  --res_backward_subs                     full
% 1.69/1.01  --res_forward_subs_resolution           true
% 1.69/1.01  --res_backward_subs_resolution          true
% 1.69/1.01  --res_orphan_elimination                true
% 1.69/1.01  --res_time_limit                        2.
% 1.69/1.01  --res_out_proof                         true
% 1.69/1.01  
% 1.69/1.01  ------ Superposition Options
% 1.69/1.01  
% 1.69/1.01  --superposition_flag                    true
% 1.69/1.01  --sup_passive_queue_type                priority_queues
% 1.69/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.69/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.69/1.01  --demod_completeness_check              fast
% 1.69/1.01  --demod_use_ground                      true
% 1.69/1.01  --sup_to_prop_solver                    passive
% 1.69/1.01  --sup_prop_simpl_new                    true
% 1.69/1.01  --sup_prop_simpl_given                  true
% 1.69/1.01  --sup_fun_splitting                     false
% 1.69/1.01  --sup_smt_interval                      50000
% 1.69/1.01  
% 1.69/1.01  ------ Superposition Simplification Setup
% 1.69/1.01  
% 1.69/1.01  --sup_indices_passive                   []
% 1.69/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.69/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.69/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.69/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.69/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.69/1.01  --sup_full_bw                           [BwDemod]
% 1.69/1.01  --sup_immed_triv                        [TrivRules]
% 1.69/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.69/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.69/1.01  --sup_immed_bw_main                     []
% 1.69/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.69/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.69/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.69/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.69/1.01  
% 1.69/1.01  ------ Combination Options
% 1.69/1.01  
% 1.69/1.01  --comb_res_mult                         3
% 1.69/1.01  --comb_sup_mult                         2
% 1.69/1.01  --comb_inst_mult                        10
% 1.69/1.01  
% 1.69/1.01  ------ Debug Options
% 1.69/1.01  
% 1.69/1.01  --dbg_backtrace                         false
% 1.69/1.01  --dbg_dump_prop_clauses                 false
% 1.69/1.01  --dbg_dump_prop_clauses_file            -
% 1.69/1.01  --dbg_out_stat                          false
% 1.69/1.01  ------ Parsing...
% 1.69/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.69/1.01  
% 1.69/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.69/1.01  
% 1.69/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.69/1.01  
% 1.69/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.69/1.01  ------ Proving...
% 1.69/1.01  ------ Problem Properties 
% 1.69/1.01  
% 1.69/1.01  
% 1.69/1.01  clauses                                 34
% 1.69/1.01  conjectures                             2
% 1.69/1.01  EPR                                     4
% 1.69/1.01  Horn                                    26
% 1.69/1.01  unary                                   15
% 1.69/1.01  binary                                  6
% 1.69/1.01  lits                                    70
% 1.69/1.01  lits eq                                 32
% 1.69/1.01  fd_pure                                 0
% 1.69/1.01  fd_pseudo                               0
% 1.69/1.01  fd_cond                                 0
% 1.69/1.01  fd_pseudo_cond                          10
% 1.69/1.01  AC symbols                              0
% 1.69/1.01  
% 1.69/1.01  ------ Schedule dynamic 5 is on 
% 1.69/1.01  
% 1.69/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.69/1.01  
% 1.69/1.01  
% 1.69/1.01  ------ 
% 1.69/1.01  Current options:
% 1.69/1.01  ------ 
% 1.69/1.01  
% 1.69/1.01  ------ Input Options
% 1.69/1.01  
% 1.69/1.01  --out_options                           all
% 1.69/1.01  --tptp_safe_out                         true
% 1.69/1.01  --problem_path                          ""
% 1.69/1.01  --include_path                          ""
% 1.69/1.01  --clausifier                            res/vclausify_rel
% 1.69/1.01  --clausifier_options                    --mode clausify
% 1.69/1.01  --stdin                                 false
% 1.69/1.01  --stats_out                             all
% 1.69/1.01  
% 1.69/1.01  ------ General Options
% 1.69/1.01  
% 1.69/1.01  --fof                                   false
% 1.69/1.01  --time_out_real                         305.
% 1.69/1.01  --time_out_virtual                      -1.
% 1.69/1.01  --symbol_type_check                     false
% 1.69/1.01  --clausify_out                          false
% 1.69/1.01  --sig_cnt_out                           false
% 1.69/1.01  --trig_cnt_out                          false
% 1.69/1.01  --trig_cnt_out_tolerance                1.
% 1.69/1.01  --trig_cnt_out_sk_spl                   false
% 1.69/1.01  --abstr_cl_out                          false
% 1.69/1.01  
% 1.69/1.01  ------ Global Options
% 1.69/1.01  
% 1.69/1.01  --schedule                              default
% 1.69/1.01  --add_important_lit                     false
% 1.69/1.01  --prop_solver_per_cl                    1000
% 1.69/1.01  --min_unsat_core                        false
% 1.69/1.01  --soft_assumptions                      false
% 1.69/1.01  --soft_lemma_size                       3
% 1.69/1.01  --prop_impl_unit_size                   0
% 1.69/1.01  --prop_impl_unit                        []
% 1.69/1.01  --share_sel_clauses                     true
% 1.69/1.01  --reset_solvers                         false
% 1.69/1.01  --bc_imp_inh                            [conj_cone]
% 1.69/1.01  --conj_cone_tolerance                   3.
% 1.69/1.01  --extra_neg_conj                        none
% 1.69/1.01  --large_theory_mode                     true
% 1.69/1.01  --prolific_symb_bound                   200
% 1.69/1.01  --lt_threshold                          2000
% 1.69/1.01  --clause_weak_htbl                      true
% 1.69/1.01  --gc_record_bc_elim                     false
% 1.69/1.01  
% 1.69/1.01  ------ Preprocessing Options
% 1.69/1.01  
% 1.69/1.01  --preprocessing_flag                    true
% 1.69/1.01  --time_out_prep_mult                    0.1
% 1.69/1.01  --splitting_mode                        input
% 1.69/1.01  --splitting_grd                         true
% 1.69/1.01  --splitting_cvd                         false
% 1.69/1.01  --splitting_cvd_svl                     false
% 1.69/1.01  --splitting_nvd                         32
% 1.69/1.01  --sub_typing                            true
% 1.69/1.01  --prep_gs_sim                           true
% 1.69/1.01  --prep_unflatten                        true
% 1.69/1.01  --prep_res_sim                          true
% 1.69/1.01  --prep_upred                            true
% 1.69/1.01  --prep_sem_filter                       exhaustive
% 1.69/1.01  --prep_sem_filter_out                   false
% 1.69/1.01  --pred_elim                             true
% 1.69/1.01  --res_sim_input                         true
% 1.69/1.01  --eq_ax_congr_red                       true
% 1.69/1.01  --pure_diseq_elim                       true
% 1.69/1.01  --brand_transform                       false
% 1.69/1.01  --non_eq_to_eq                          false
% 1.69/1.01  --prep_def_merge                        true
% 1.69/1.01  --prep_def_merge_prop_impl              false
% 1.69/1.01  --prep_def_merge_mbd                    true
% 1.69/1.01  --prep_def_merge_tr_red                 false
% 1.69/1.01  --prep_def_merge_tr_cl                  false
% 1.69/1.01  --smt_preprocessing                     true
% 1.69/1.01  --smt_ac_axioms                         fast
% 1.69/1.01  --preprocessed_out                      false
% 1.69/1.01  --preprocessed_stats                    false
% 1.69/1.01  
% 1.69/1.01  ------ Abstraction refinement Options
% 1.69/1.01  
% 1.69/1.01  --abstr_ref                             []
% 1.69/1.01  --abstr_ref_prep                        false
% 1.69/1.01  --abstr_ref_until_sat                   false
% 1.69/1.01  --abstr_ref_sig_restrict                funpre
% 1.69/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.69/1.01  --abstr_ref_under                       []
% 1.69/1.01  
% 1.69/1.01  ------ SAT Options
% 1.69/1.01  
% 1.69/1.01  --sat_mode                              false
% 1.69/1.01  --sat_fm_restart_options                ""
% 1.69/1.01  --sat_gr_def                            false
% 1.69/1.01  --sat_epr_types                         true
% 1.69/1.01  --sat_non_cyclic_types                  false
% 1.69/1.01  --sat_finite_models                     false
% 1.69/1.01  --sat_fm_lemmas                         false
% 1.69/1.01  --sat_fm_prep                           false
% 1.69/1.01  --sat_fm_uc_incr                        true
% 1.69/1.01  --sat_out_model                         small
% 1.69/1.01  --sat_out_clauses                       false
% 1.69/1.01  
% 1.69/1.01  ------ QBF Options
% 1.69/1.01  
% 1.69/1.01  --qbf_mode                              false
% 1.69/1.01  --qbf_elim_univ                         false
% 1.69/1.01  --qbf_dom_inst                          none
% 1.69/1.01  --qbf_dom_pre_inst                      false
% 1.69/1.01  --qbf_sk_in                             false
% 1.69/1.01  --qbf_pred_elim                         true
% 1.69/1.01  --qbf_split                             512
% 1.69/1.01  
% 1.69/1.01  ------ BMC1 Options
% 1.69/1.01  
% 1.69/1.01  --bmc1_incremental                      false
% 1.69/1.01  --bmc1_axioms                           reachable_all
% 1.69/1.01  --bmc1_min_bound                        0
% 1.69/1.01  --bmc1_max_bound                        -1
% 1.69/1.01  --bmc1_max_bound_default                -1
% 1.69/1.01  --bmc1_symbol_reachability              true
% 1.69/1.01  --bmc1_property_lemmas                  false
% 1.69/1.01  --bmc1_k_induction                      false
% 1.69/1.01  --bmc1_non_equiv_states                 false
% 1.69/1.01  --bmc1_deadlock                         false
% 1.69/1.01  --bmc1_ucm                              false
% 1.69/1.01  --bmc1_add_unsat_core                   none
% 1.69/1.01  --bmc1_unsat_core_children              false
% 1.69/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.69/1.01  --bmc1_out_stat                         full
% 1.69/1.01  --bmc1_ground_init                      false
% 1.69/1.01  --bmc1_pre_inst_next_state              false
% 1.69/1.01  --bmc1_pre_inst_state                   false
% 1.69/1.01  --bmc1_pre_inst_reach_state             false
% 1.69/1.01  --bmc1_out_unsat_core                   false
% 1.69/1.01  --bmc1_aig_witness_out                  false
% 1.69/1.01  --bmc1_verbose                          false
% 1.69/1.01  --bmc1_dump_clauses_tptp                false
% 1.69/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.69/1.01  --bmc1_dump_file                        -
% 1.69/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.69/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.69/1.01  --bmc1_ucm_extend_mode                  1
% 1.69/1.01  --bmc1_ucm_init_mode                    2
% 1.69/1.01  --bmc1_ucm_cone_mode                    none
% 1.69/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.69/1.01  --bmc1_ucm_relax_model                  4
% 1.69/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.69/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.69/1.01  --bmc1_ucm_layered_model                none
% 1.69/1.01  --bmc1_ucm_max_lemma_size               10
% 1.69/1.01  
% 1.69/1.01  ------ AIG Options
% 1.69/1.01  
% 1.69/1.01  --aig_mode                              false
% 1.69/1.01  
% 1.69/1.01  ------ Instantiation Options
% 1.69/1.01  
% 1.69/1.01  --instantiation_flag                    true
% 1.69/1.01  --inst_sos_flag                         false
% 1.69/1.01  --inst_sos_phase                        true
% 1.69/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.69/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.69/1.01  --inst_lit_sel_side                     none
% 1.69/1.01  --inst_solver_per_active                1400
% 1.69/1.01  --inst_solver_calls_frac                1.
% 1.69/1.01  --inst_passive_queue_type               priority_queues
% 1.69/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.69/1.01  --inst_passive_queues_freq              [25;2]
% 1.69/1.01  --inst_dismatching                      true
% 1.69/1.01  --inst_eager_unprocessed_to_passive     true
% 1.69/1.01  --inst_prop_sim_given                   true
% 1.69/1.01  --inst_prop_sim_new                     false
% 1.69/1.01  --inst_subs_new                         false
% 1.69/1.01  --inst_eq_res_simp                      false
% 1.69/1.01  --inst_subs_given                       false
% 1.69/1.01  --inst_orphan_elimination               true
% 1.69/1.01  --inst_learning_loop_flag               true
% 1.69/1.01  --inst_learning_start                   3000
% 1.69/1.01  --inst_learning_factor                  2
% 1.69/1.01  --inst_start_prop_sim_after_learn       3
% 1.69/1.01  --inst_sel_renew                        solver
% 1.69/1.01  --inst_lit_activity_flag                true
% 1.69/1.01  --inst_restr_to_given                   false
% 1.69/1.01  --inst_activity_threshold               500
% 1.69/1.01  --inst_out_proof                        true
% 1.69/1.01  
% 1.69/1.01  ------ Resolution Options
% 1.69/1.01  
% 1.69/1.01  --resolution_flag                       false
% 1.69/1.01  --res_lit_sel                           adaptive
% 1.69/1.01  --res_lit_sel_side                      none
% 1.69/1.01  --res_ordering                          kbo
% 1.69/1.01  --res_to_prop_solver                    active
% 1.69/1.01  --res_prop_simpl_new                    false
% 1.69/1.01  --res_prop_simpl_given                  true
% 1.69/1.01  --res_passive_queue_type                priority_queues
% 1.69/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.69/1.01  --res_passive_queues_freq               [15;5]
% 1.69/1.01  --res_forward_subs                      full
% 1.69/1.01  --res_backward_subs                     full
% 1.69/1.01  --res_forward_subs_resolution           true
% 1.69/1.01  --res_backward_subs_resolution          true
% 1.69/1.01  --res_orphan_elimination                true
% 1.69/1.01  --res_time_limit                        2.
% 1.69/1.01  --res_out_proof                         true
% 1.69/1.01  
% 1.69/1.01  ------ Superposition Options
% 1.69/1.01  
% 1.69/1.01  --superposition_flag                    true
% 1.69/1.01  --sup_passive_queue_type                priority_queues
% 1.69/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.69/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.69/1.01  --demod_completeness_check              fast
% 1.69/1.01  --demod_use_ground                      true
% 1.69/1.01  --sup_to_prop_solver                    passive
% 1.69/1.01  --sup_prop_simpl_new                    true
% 1.69/1.01  --sup_prop_simpl_given                  true
% 1.69/1.01  --sup_fun_splitting                     false
% 1.69/1.01  --sup_smt_interval                      50000
% 1.69/1.01  
% 1.69/1.01  ------ Superposition Simplification Setup
% 1.69/1.01  
% 1.69/1.01  --sup_indices_passive                   []
% 1.69/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.69/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.69/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.69/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.69/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.69/1.01  --sup_full_bw                           [BwDemod]
% 1.69/1.01  --sup_immed_triv                        [TrivRules]
% 1.69/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.69/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.69/1.01  --sup_immed_bw_main                     []
% 1.69/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.69/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.69/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.69/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.69/1.01  
% 1.69/1.01  ------ Combination Options
% 1.69/1.01  
% 1.69/1.01  --comb_res_mult                         3
% 1.69/1.01  --comb_sup_mult                         2
% 1.69/1.01  --comb_inst_mult                        10
% 1.69/1.01  
% 1.69/1.01  ------ Debug Options
% 1.69/1.01  
% 1.69/1.01  --dbg_backtrace                         false
% 1.69/1.01  --dbg_dump_prop_clauses                 false
% 1.69/1.01  --dbg_dump_prop_clauses_file            -
% 1.69/1.01  --dbg_out_stat                          false
% 1.69/1.01  
% 1.69/1.01  
% 1.69/1.01  
% 1.69/1.01  
% 1.69/1.01  ------ Proving...
% 1.69/1.01  
% 1.69/1.01  
% 1.69/1.01  % SZS status Theorem for theBenchmark.p
% 1.69/1.01  
% 1.69/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.69/1.01  
% 1.69/1.01  fof(f3,axiom,(
% 1.69/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.69/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/1.01  
% 1.69/1.01  fof(f24,plain,(
% 1.69/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.69/1.01    inference(ennf_transformation,[],[f3])).
% 1.69/1.01  
% 1.69/1.01  fof(f28,plain,(
% 1.69/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.69/1.01    inference(nnf_transformation,[],[f24])).
% 1.69/1.01  
% 1.69/1.01  fof(f29,plain,(
% 1.69/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.69/1.01    inference(rectify,[],[f28])).
% 1.69/1.01  
% 1.69/1.01  fof(f30,plain,(
% 1.69/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.69/1.01    introduced(choice_axiom,[])).
% 1.69/1.01  
% 1.69/1.01  fof(f31,plain,(
% 1.69/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.69/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 1.69/1.01  
% 1.69/1.01  fof(f52,plain,(
% 1.69/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.69/1.01    inference(cnf_transformation,[],[f31])).
% 1.69/1.01  
% 1.69/1.01  fof(f2,axiom,(
% 1.69/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.69/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/1.01  
% 1.69/1.01  fof(f51,plain,(
% 1.69/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.69/1.01    inference(cnf_transformation,[],[f2])).
% 1.69/1.01  
% 1.69/1.01  fof(f22,conjecture,(
% 1.69/1.01    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 1.69/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/1.01  
% 1.69/1.01  fof(f23,negated_conjecture,(
% 1.69/1.01    ~! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 1.69/1.01    inference(negated_conjecture,[],[f22])).
% 1.69/1.01  
% 1.69/1.01  fof(f27,plain,(
% 1.69/1.01    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 1.69/1.01    inference(ennf_transformation,[],[f23])).
% 1.69/1.01  
% 1.69/1.01  fof(f48,plain,(
% 1.69/1.01    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK4 != sK5 & k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4))),
% 1.69/1.01    introduced(choice_axiom,[])).
% 1.69/1.01  
% 1.69/1.01  fof(f49,plain,(
% 1.69/1.01    sK4 != sK5 & k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4)),
% 1.69/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f27,f48])).
% 1.69/1.01  
% 1.69/1.01  fof(f90,plain,(
% 1.69/1.01    k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4)),
% 1.69/1.01    inference(cnf_transformation,[],[f49])).
% 1.69/1.01  
% 1.69/1.01  fof(f10,axiom,(
% 1.69/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.69/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/1.01  
% 1.69/1.01  fof(f68,plain,(
% 1.69/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.69/1.01    inference(cnf_transformation,[],[f10])).
% 1.69/1.01  
% 1.69/1.01  fof(f6,axiom,(
% 1.69/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.69/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/1.01  
% 1.69/1.01  fof(f64,plain,(
% 1.69/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.69/1.01    inference(cnf_transformation,[],[f6])).
% 1.69/1.01  
% 1.69/1.01  fof(f92,plain,(
% 1.69/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.69/1.01    inference(definition_unfolding,[],[f68,f64])).
% 1.69/1.01  
% 1.69/1.01  fof(f17,axiom,(
% 1.69/1.01    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.69/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/1.01  
% 1.69/1.01  fof(f85,plain,(
% 1.69/1.01    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.69/1.01    inference(cnf_transformation,[],[f17])).
% 1.69/1.01  
% 1.69/1.01  fof(f122,plain,(
% 1.69/1.01    k5_xboole_0(k2_tarski(sK4,sK4),k5_xboole_0(k2_tarski(sK5,sK5),k3_xboole_0(k2_tarski(sK5,sK5),k2_tarski(sK4,sK4)))) = k2_tarski(sK4,sK4)),
% 1.69/1.01    inference(definition_unfolding,[],[f90,f92,f85,f85,f85])).
% 1.69/1.01  
% 1.69/1.01  fof(f1,axiom,(
% 1.69/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.69/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/1.01  
% 1.69/1.01  fof(f50,plain,(
% 1.69/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.69/1.01    inference(cnf_transformation,[],[f1])).
% 1.69/1.01  
% 1.69/1.01  fof(f99,plain,(
% 1.69/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.69/1.01    inference(definition_unfolding,[],[f50,f92,f92])).
% 1.69/1.01  
% 1.69/1.01  fof(f9,axiom,(
% 1.69/1.01    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.69/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/1.01  
% 1.69/1.01  fof(f67,plain,(
% 1.69/1.01    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.69/1.01    inference(cnf_transformation,[],[f9])).
% 1.69/1.01  
% 1.69/1.01  fof(f107,plain,(
% 1.69/1.01    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 1.69/1.01    inference(definition_unfolding,[],[f67,f92])).
% 1.69/1.01  
% 1.69/1.01  fof(f12,axiom,(
% 1.69/1.01    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.69/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/1.01  
% 1.69/1.01  fof(f44,plain,(
% 1.69/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.69/1.01    inference(nnf_transformation,[],[f12])).
% 1.69/1.01  
% 1.69/1.01  fof(f45,plain,(
% 1.69/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.69/1.01    inference(rectify,[],[f44])).
% 1.69/1.01  
% 1.69/1.01  fof(f46,plain,(
% 1.69/1.01    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 1.69/1.01    introduced(choice_axiom,[])).
% 1.69/1.01  
% 1.69/1.01  fof(f47,plain,(
% 1.69/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.69/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f45,f46])).
% 1.69/1.01  
% 1.69/1.01  fof(f78,plain,(
% 1.69/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.69/1.01    inference(cnf_transformation,[],[f47])).
% 1.69/1.01  
% 1.69/1.01  fof(f118,plain,(
% 1.69/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 1.69/1.01    inference(definition_unfolding,[],[f78,f85])).
% 1.69/1.01  
% 1.69/1.01  fof(f135,plain,(
% 1.69/1.01    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 1.69/1.01    inference(equality_resolution,[],[f118])).
% 1.69/1.01  
% 1.69/1.01  fof(f136,plain,(
% 1.69/1.01    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 1.69/1.01    inference(equality_resolution,[],[f135])).
% 1.69/1.01  
% 1.69/1.01  fof(f77,plain,(
% 1.69/1.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.69/1.01    inference(cnf_transformation,[],[f47])).
% 1.69/1.01  
% 1.69/1.01  fof(f119,plain,(
% 1.69/1.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 1.69/1.01    inference(definition_unfolding,[],[f77,f85])).
% 1.69/1.01  
% 1.69/1.01  fof(f137,plain,(
% 1.69/1.01    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_tarski(X0,X0))) )),
% 1.69/1.01    inference(equality_resolution,[],[f119])).
% 1.69/1.01  
% 1.69/1.01  fof(f91,plain,(
% 1.69/1.01    sK4 != sK5),
% 1.69/1.01    inference(cnf_transformation,[],[f49])).
% 1.69/1.01  
% 1.69/1.01  cnf(c_6,plain,
% 1.69/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 1.69/1.01      inference(cnf_transformation,[],[f52]) ).
% 1.69/1.01  
% 1.69/1.01  cnf(c_1928,plain,
% 1.69/1.01      ( ~ r2_hidden(sK5,X0)
% 1.69/1.01      | r2_hidden(sK5,k2_tarski(X1,X1))
% 1.69/1.01      | ~ r1_tarski(X0,k2_tarski(X1,X1)) ),
% 1.69/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 1.69/1.01  
% 1.69/1.01  cnf(c_3972,plain,
% 1.69/1.01      ( r2_hidden(sK5,k2_tarski(X0,X0))
% 1.69/1.01      | ~ r2_hidden(sK5,k2_tarski(sK5,sK5))
% 1.69/1.01      | ~ r1_tarski(k2_tarski(sK5,sK5),k2_tarski(X0,X0)) ),
% 1.69/1.01      inference(instantiation,[status(thm)],[c_1928]) ).
% 1.69/1.01  
% 1.69/1.01  cnf(c_3974,plain,
% 1.69/1.01      ( ~ r2_hidden(sK5,k2_tarski(sK5,sK5))
% 1.69/1.01      | r2_hidden(sK5,k2_tarski(sK4,sK4))
% 1.69/1.01      | ~ r1_tarski(k2_tarski(sK5,sK5),k2_tarski(sK4,sK4)) ),
% 1.69/1.01      inference(instantiation,[status(thm)],[c_3972]) ).
% 1.69/1.01  
% 1.69/1.01  cnf(c_3,plain,
% 1.69/1.01      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 1.69/1.01      inference(cnf_transformation,[],[f51]) ).
% 1.69/1.01  
% 1.69/1.01  cnf(c_34,negated_conjecture,
% 1.69/1.01      ( k5_xboole_0(k2_tarski(sK4,sK4),k5_xboole_0(k2_tarski(sK5,sK5),k3_xboole_0(k2_tarski(sK5,sK5),k2_tarski(sK4,sK4)))) = k2_tarski(sK4,sK4) ),
% 1.69/1.01      inference(cnf_transformation,[],[f122]) ).
% 1.69/1.01  
% 1.69/1.01  cnf(c_1124,plain,
% 1.69/1.01      ( k5_xboole_0(k2_tarski(sK4,sK4),k5_xboole_0(k2_tarski(sK5,sK5),k3_xboole_0(k2_tarski(sK4,sK4),k2_tarski(sK5,sK5)))) = k2_tarski(sK4,sK4) ),
% 1.69/1.01      inference(demodulation,[status(thm)],[c_3,c_34]) ).
% 1.69/1.01  
% 1.69/1.01  cnf(c_2,plain,
% 1.69/1.01      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 1.69/1.01      inference(cnf_transformation,[],[f99]) ).
% 1.69/1.01  
% 1.69/1.01  cnf(c_18,plain,
% 1.69/1.01      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
% 1.69/1.01      inference(cnf_transformation,[],[f107]) ).
% 1.69/1.01  
% 1.69/1.01  cnf(c_868,plain,
% 1.69/1.01      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = iProver_top ),
% 1.69/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.69/1.01  
% 1.69/1.01  cnf(c_2194,plain,
% 1.69/1.01      ( r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = iProver_top ),
% 1.69/1.01      inference(superposition,[status(thm)],[c_2,c_868]) ).
% 1.69/1.01  
% 1.69/1.01  cnf(c_2332,plain,
% 1.69/1.01      ( r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = iProver_top ),
% 1.69/1.01      inference(superposition,[status(thm)],[c_3,c_2194]) ).
% 1.69/1.01  
% 1.69/1.01  cnf(c_2654,plain,
% 1.69/1.01      ( r1_tarski(k2_tarski(sK5,sK5),k2_tarski(sK4,sK4)) = iProver_top ),
% 1.69/1.01      inference(superposition,[status(thm)],[c_1124,c_2332]) ).
% 1.69/1.01  
% 1.69/1.01  cnf(c_2661,plain,
% 1.69/1.01      ( r1_tarski(k2_tarski(sK5,sK5),k2_tarski(sK4,sK4)) ),
% 1.69/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_2654]) ).
% 1.69/1.01  
% 1.69/1.01  cnf(c_29,plain,
% 1.69/1.01      ( r2_hidden(X0,k2_tarski(X0,X0)) ),
% 1.69/1.01      inference(cnf_transformation,[],[f136]) ).
% 1.69/1.01  
% 1.69/1.01  cnf(c_1400,plain,
% 1.69/1.01      ( r2_hidden(sK5,k2_tarski(sK5,sK5)) ),
% 1.69/1.01      inference(instantiation,[status(thm)],[c_29]) ).
% 1.69/1.01  
% 1.69/1.01  cnf(c_30,plain,
% 1.69/1.01      ( ~ r2_hidden(X0,k2_tarski(X1,X1)) | X0 = X1 ),
% 1.69/1.01      inference(cnf_transformation,[],[f137]) ).
% 1.69/1.01  
% 1.69/1.01  cnf(c_1197,plain,
% 1.69/1.01      ( ~ r2_hidden(sK5,k2_tarski(X0,X0)) | sK5 = X0 ),
% 1.69/1.01      inference(instantiation,[status(thm)],[c_30]) ).
% 1.69/1.01  
% 1.69/1.01  cnf(c_1199,plain,
% 1.69/1.01      ( ~ r2_hidden(sK5,k2_tarski(sK4,sK4)) | sK5 = sK4 ),
% 1.69/1.01      inference(instantiation,[status(thm)],[c_1197]) ).
% 1.69/1.01  
% 1.69/1.01  cnf(c_456,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.69/1.01  
% 1.69/1.01  cnf(c_1109,plain,
% 1.69/1.01      ( sK5 != X0 | sK4 != X0 | sK4 = sK5 ),
% 1.69/1.01      inference(instantiation,[status(thm)],[c_456]) ).
% 1.69/1.01  
% 1.69/1.01  cnf(c_1110,plain,
% 1.69/1.01      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 1.69/1.01      inference(instantiation,[status(thm)],[c_1109]) ).
% 1.69/1.01  
% 1.69/1.01  cnf(c_41,plain,
% 1.69/1.01      ( r2_hidden(sK4,k2_tarski(sK4,sK4)) ),
% 1.69/1.01      inference(instantiation,[status(thm)],[c_29]) ).
% 1.69/1.02  
% 1.69/1.02  cnf(c_38,plain,
% 1.69/1.02      ( ~ r2_hidden(sK4,k2_tarski(sK4,sK4)) | sK4 = sK4 ),
% 1.69/1.02      inference(instantiation,[status(thm)],[c_30]) ).
% 1.69/1.02  
% 1.69/1.02  cnf(c_33,negated_conjecture,
% 1.69/1.02      ( sK4 != sK5 ),
% 1.69/1.02      inference(cnf_transformation,[],[f91]) ).
% 1.69/1.02  
% 1.69/1.02  cnf(contradiction,plain,
% 1.69/1.02      ( $false ),
% 1.69/1.02      inference(minisat,
% 1.69/1.02                [status(thm)],
% 1.69/1.02                [c_3974,c_2661,c_1400,c_1199,c_1110,c_41,c_38,c_33]) ).
% 1.69/1.02  
% 1.69/1.02  
% 1.69/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 1.69/1.02  
% 1.69/1.02  ------                               Statistics
% 1.69/1.02  
% 1.69/1.02  ------ General
% 1.69/1.02  
% 1.69/1.02  abstr_ref_over_cycles:                  0
% 1.69/1.02  abstr_ref_under_cycles:                 0
% 1.69/1.02  gc_basic_clause_elim:                   0
% 1.69/1.02  forced_gc_time:                         0
% 1.69/1.02  parsing_time:                           0.008
% 1.69/1.02  unif_index_cands_time:                  0.
% 1.69/1.02  unif_index_add_time:                    0.
% 1.69/1.02  orderings_time:                         0.
% 1.69/1.02  out_proof_time:                         0.009
% 1.69/1.02  total_time:                             0.145
% 1.69/1.02  num_of_symbols:                         45
% 1.69/1.02  num_of_terms:                           5383
% 1.69/1.02  
% 1.69/1.02  ------ Preprocessing
% 1.69/1.02  
% 1.69/1.02  num_of_splits:                          0
% 1.69/1.02  num_of_split_atoms:                     0
% 1.69/1.02  num_of_reused_defs:                     0
% 1.69/1.02  num_eq_ax_congr_red:                    69
% 1.69/1.02  num_of_sem_filtered_clauses:            1
% 1.69/1.02  num_of_subtypes:                        0
% 1.69/1.02  monotx_restored_types:                  0
% 1.69/1.02  sat_num_of_epr_types:                   0
% 1.69/1.02  sat_num_of_non_cyclic_types:            0
% 1.69/1.02  sat_guarded_non_collapsed_types:        0
% 1.69/1.02  num_pure_diseq_elim:                    0
% 1.69/1.02  simp_replaced_by:                       0
% 1.69/1.02  res_preprocessed:                       151
% 1.69/1.02  prep_upred:                             0
% 1.69/1.02  prep_unflattend:                        0
% 1.69/1.02  smt_new_axioms:                         0
% 1.69/1.02  pred_elim_cands:                        2
% 1.69/1.02  pred_elim:                              0
% 1.69/1.02  pred_elim_cl:                           0
% 1.69/1.02  pred_elim_cycles:                       2
% 1.69/1.02  merged_defs:                            0
% 1.69/1.02  merged_defs_ncl:                        0
% 1.69/1.02  bin_hyper_res:                          0
% 1.69/1.02  prep_cycles:                            4
% 1.69/1.02  pred_elim_time:                         0.
% 1.69/1.02  splitting_time:                         0.
% 1.69/1.02  sem_filter_time:                        0.
% 1.69/1.02  monotx_time:                            0.
% 1.69/1.02  subtype_inf_time:                       0.
% 1.69/1.02  
% 1.69/1.02  ------ Problem properties
% 1.69/1.02  
% 1.69/1.02  clauses:                                34
% 1.69/1.02  conjectures:                            2
% 1.69/1.02  epr:                                    4
% 1.69/1.02  horn:                                   26
% 1.69/1.02  ground:                                 2
% 1.69/1.02  unary:                                  15
% 1.69/1.02  binary:                                 6
% 1.69/1.02  lits:                                   70
% 1.69/1.02  lits_eq:                                32
% 1.69/1.02  fd_pure:                                0
% 1.69/1.02  fd_pseudo:                              0
% 1.69/1.02  fd_cond:                                0
% 1.69/1.02  fd_pseudo_cond:                         10
% 1.69/1.02  ac_symbols:                             0
% 1.69/1.02  
% 1.69/1.02  ------ Propositional Solver
% 1.69/1.02  
% 1.69/1.02  prop_solver_calls:                      26
% 1.69/1.02  prop_fast_solver_calls:                 689
% 1.69/1.02  smt_solver_calls:                       0
% 1.69/1.02  smt_fast_solver_calls:                  0
% 1.69/1.02  prop_num_of_clauses:                    1686
% 1.69/1.02  prop_preprocess_simplified:             6929
% 1.69/1.02  prop_fo_subsumed:                       0
% 1.69/1.02  prop_solver_time:                       0.
% 1.69/1.02  smt_solver_time:                        0.
% 1.69/1.02  smt_fast_solver_time:                   0.
% 1.69/1.02  prop_fast_solver_time:                  0.
% 1.69/1.02  prop_unsat_core_time:                   0.
% 1.69/1.02  
% 1.69/1.02  ------ QBF
% 1.69/1.02  
% 1.69/1.02  qbf_q_res:                              0
% 1.69/1.02  qbf_num_tautologies:                    0
% 1.69/1.02  qbf_prep_cycles:                        0
% 1.69/1.02  
% 1.69/1.02  ------ BMC1
% 1.69/1.02  
% 1.69/1.02  bmc1_current_bound:                     -1
% 1.69/1.02  bmc1_last_solved_bound:                 -1
% 1.69/1.02  bmc1_unsat_core_size:                   -1
% 1.69/1.02  bmc1_unsat_core_parents_size:           -1
% 1.69/1.02  bmc1_merge_next_fun:                    0
% 1.69/1.02  bmc1_unsat_core_clauses_time:           0.
% 1.69/1.02  
% 1.69/1.02  ------ Instantiation
% 1.69/1.02  
% 1.69/1.02  inst_num_of_clauses:                    511
% 1.69/1.02  inst_num_in_passive:                    210
% 1.69/1.02  inst_num_in_active:                     152
% 1.69/1.02  inst_num_in_unprocessed:                148
% 1.69/1.02  inst_num_of_loops:                      194
% 1.69/1.02  inst_num_of_learning_restarts:          0
% 1.69/1.02  inst_num_moves_active_passive:          40
% 1.69/1.02  inst_lit_activity:                      0
% 1.69/1.02  inst_lit_activity_moves:                0
% 1.69/1.02  inst_num_tautologies:                   0
% 1.69/1.02  inst_num_prop_implied:                  0
% 1.69/1.02  inst_num_existing_simplified:           0
% 1.69/1.02  inst_num_eq_res_simplified:             0
% 1.69/1.02  inst_num_child_elim:                    0
% 1.69/1.02  inst_num_of_dismatching_blockings:      91
% 1.69/1.02  inst_num_of_non_proper_insts:           351
% 1.69/1.02  inst_num_of_duplicates:                 0
% 1.69/1.02  inst_inst_num_from_inst_to_res:         0
% 1.69/1.02  inst_dismatching_checking_time:         0.
% 1.69/1.02  
% 1.69/1.02  ------ Resolution
% 1.69/1.02  
% 1.69/1.02  res_num_of_clauses:                     0
% 1.69/1.02  res_num_in_passive:                     0
% 1.69/1.02  res_num_in_active:                      0
% 1.69/1.02  res_num_of_loops:                       155
% 1.69/1.02  res_forward_subset_subsumed:            51
% 1.69/1.02  res_backward_subset_subsumed:           0
% 1.69/1.02  res_forward_subsumed:                   0
% 1.69/1.02  res_backward_subsumed:                  0
% 1.69/1.02  res_forward_subsumption_resolution:     0
% 1.69/1.02  res_backward_subsumption_resolution:    0
% 1.69/1.02  res_clause_to_clause_subsumption:       244
% 1.69/1.02  res_orphan_elimination:                 0
% 1.69/1.02  res_tautology_del:                      11
% 1.69/1.02  res_num_eq_res_simplified:              0
% 1.69/1.02  res_num_sel_changes:                    0
% 1.69/1.02  res_moves_from_active_to_pass:          0
% 1.69/1.02  
% 1.69/1.02  ------ Superposition
% 1.69/1.02  
% 1.69/1.02  sup_time_total:                         0.
% 1.69/1.02  sup_time_generating:                    0.
% 1.69/1.02  sup_time_sim_full:                      0.
% 1.69/1.02  sup_time_sim_immed:                     0.
% 1.69/1.02  
% 1.69/1.02  sup_num_of_clauses:                     79
% 1.69/1.02  sup_num_in_active:                      36
% 1.69/1.02  sup_num_in_passive:                     43
% 1.69/1.02  sup_num_of_loops:                       38
% 1.69/1.02  sup_fw_superposition:                   82
% 1.69/1.02  sup_bw_superposition:                   35
% 1.69/1.02  sup_immediate_simplified:               9
% 1.69/1.02  sup_given_eliminated:                   0
% 1.69/1.02  comparisons_done:                       0
% 1.69/1.02  comparisons_avoided:                    2
% 1.69/1.02  
% 1.69/1.02  ------ Simplifications
% 1.69/1.02  
% 1.69/1.02  
% 1.69/1.02  sim_fw_subset_subsumed:                 0
% 1.69/1.02  sim_bw_subset_subsumed:                 0
% 1.69/1.02  sim_fw_subsumed:                        6
% 1.69/1.02  sim_bw_subsumed:                        0
% 1.69/1.02  sim_fw_subsumption_res:                 0
% 1.69/1.02  sim_bw_subsumption_res:                 0
% 1.69/1.02  sim_tautology_del:                      0
% 1.69/1.02  sim_eq_tautology_del:                   1
% 1.69/1.02  sim_eq_res_simp:                        0
% 1.69/1.02  sim_fw_demodulated:                     6
% 1.69/1.02  sim_bw_demodulated:                     5
% 1.69/1.02  sim_light_normalised:                   5
% 1.69/1.02  sim_joinable_taut:                      0
% 1.69/1.02  sim_joinable_simp:                      0
% 1.69/1.02  sim_ac_normalised:                      0
% 1.69/1.02  sim_smt_subsumption:                    0
% 1.69/1.02  
%------------------------------------------------------------------------------
