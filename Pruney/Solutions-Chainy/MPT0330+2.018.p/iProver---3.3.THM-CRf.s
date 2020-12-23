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
% DateTime   : Thu Dec  3 11:38:11 EST 2020

% Result     : Theorem 10.78s
% Output     : CNFRefutation 10.78s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 135 expanded)
%              Number of clauses        :   29 (  36 expanded)
%              Number of leaves         :    9 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :  112 ( 226 expanded)
%              Number of equality atoms :   46 (  99 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1))
      & k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_tarski(k2_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(X2,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f25,f23,f23])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f21,f23,f23])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f14])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f15,f16])).

fof(f28,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f17])).

fof(f36,plain,(
    ~ r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) ),
    inference(definition_unfolding,[],[f28,f23,f23,f23])).

fof(f24,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_tarski(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) = k2_zfmisc_1(k3_tarski(k2_tarski(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f24,f23,f23])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f26,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_tarski(X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f20,f23])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k3_tarski(k2_tarski(X0,X1)),X2) ) ),
    inference(definition_unfolding,[],[f19,f23])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f18,f23,f23])).

fof(f27,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_5,plain,
    ( k3_tarski(k2_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))) = k2_zfmisc_1(X0,k3_tarski(k2_tarski(X1,X2))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X3))) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_218,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X3) != iProver_top
    | r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2819,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(X3,k2_zfmisc_1(X1,X4)) != iProver_top
    | r1_tarski(k3_tarski(k2_tarski(X0,X3)),k2_zfmisc_1(X1,k3_tarski(k2_tarski(X2,X4)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_218])).

cnf(c_7,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_216,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_28529,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK5)) != iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2819,c_216])).

cnf(c_6,plain,
    ( k3_tarski(k2_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(k3_tarski(k2_tarski(X0,X2)),X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_4,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_217,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_847,plain,
    ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k3_tarski(k2_tarski(X0,X2)),X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_217])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_214,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k2_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_219,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_692,plain,
    ( k3_tarski(k2_tarski(sK0,k2_zfmisc_1(sK2,sK3))) = k2_zfmisc_1(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_214,c_219])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_220,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4108,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK3),X0) != iProver_top
    | r1_tarski(sK0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_692,c_220])).

cnf(c_4980,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,X0)),sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_847,c_4108])).

cnf(c_0,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_424,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_217])).

cnf(c_848,plain,
    ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k3_tarski(k2_tarski(X2,X0)),X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_424])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_215,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_691,plain,
    ( k3_tarski(k2_tarski(sK1,k2_zfmisc_1(sK4,sK5))) = k2_zfmisc_1(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_215,c_219])).

cnf(c_4107,plain,
    ( r1_tarski(k2_zfmisc_1(sK4,sK5),X0) != iProver_top
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_691,c_220])).

cnf(c_4914,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(X0,sK4)),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_848,c_4107])).

cnf(c_34598,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_28529,c_4980,c_4914])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:49:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 10.78/1.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.78/1.98  
% 10.78/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 10.78/1.98  
% 10.78/1.98  ------  iProver source info
% 10.78/1.98  
% 10.78/1.98  git: date: 2020-06-30 10:37:57 +0100
% 10.78/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 10.78/1.98  git: non_committed_changes: false
% 10.78/1.98  git: last_make_outside_of_git: false
% 10.78/1.98  
% 10.78/1.98  ------ 
% 10.78/1.98  
% 10.78/1.98  ------ Input Options
% 10.78/1.98  
% 10.78/1.98  --out_options                           all
% 10.78/1.98  --tptp_safe_out                         true
% 10.78/1.98  --problem_path                          ""
% 10.78/1.98  --include_path                          ""
% 10.78/1.98  --clausifier                            res/vclausify_rel
% 10.78/1.98  --clausifier_options                    --mode clausify
% 10.78/1.98  --stdin                                 false
% 10.78/1.98  --stats_out                             all
% 10.78/1.98  
% 10.78/1.98  ------ General Options
% 10.78/1.98  
% 10.78/1.98  --fof                                   false
% 10.78/1.98  --time_out_real                         305.
% 10.78/1.98  --time_out_virtual                      -1.
% 10.78/1.98  --symbol_type_check                     false
% 10.78/1.98  --clausify_out                          false
% 10.78/1.98  --sig_cnt_out                           false
% 10.78/1.98  --trig_cnt_out                          false
% 10.78/1.98  --trig_cnt_out_tolerance                1.
% 10.78/1.98  --trig_cnt_out_sk_spl                   false
% 10.78/1.98  --abstr_cl_out                          false
% 10.78/1.98  
% 10.78/1.98  ------ Global Options
% 10.78/1.98  
% 10.78/1.98  --schedule                              default
% 10.78/1.98  --add_important_lit                     false
% 10.78/1.98  --prop_solver_per_cl                    1000
% 10.78/1.98  --min_unsat_core                        false
% 10.78/1.98  --soft_assumptions                      false
% 10.78/1.98  --soft_lemma_size                       3
% 10.78/1.98  --prop_impl_unit_size                   0
% 10.78/1.98  --prop_impl_unit                        []
% 10.78/1.98  --share_sel_clauses                     true
% 10.78/1.98  --reset_solvers                         false
% 10.78/1.98  --bc_imp_inh                            [conj_cone]
% 10.78/1.98  --conj_cone_tolerance                   3.
% 10.78/1.98  --extra_neg_conj                        none
% 10.78/1.98  --large_theory_mode                     true
% 10.78/1.98  --prolific_symb_bound                   200
% 10.78/1.98  --lt_threshold                          2000
% 10.78/1.98  --clause_weak_htbl                      true
% 10.78/1.98  --gc_record_bc_elim                     false
% 10.78/1.98  
% 10.78/1.98  ------ Preprocessing Options
% 10.78/1.98  
% 10.78/1.98  --preprocessing_flag                    true
% 10.78/1.98  --time_out_prep_mult                    0.1
% 10.78/1.98  --splitting_mode                        input
% 10.78/1.98  --splitting_grd                         true
% 10.78/1.98  --splitting_cvd                         false
% 10.78/1.98  --splitting_cvd_svl                     false
% 10.78/1.98  --splitting_nvd                         32
% 10.78/1.98  --sub_typing                            true
% 10.78/1.98  --prep_gs_sim                           true
% 10.78/1.98  --prep_unflatten                        true
% 10.78/1.98  --prep_res_sim                          true
% 10.78/1.98  --prep_upred                            true
% 10.78/1.98  --prep_sem_filter                       exhaustive
% 10.78/1.98  --prep_sem_filter_out                   false
% 10.78/1.98  --pred_elim                             true
% 10.78/1.98  --res_sim_input                         true
% 10.78/1.98  --eq_ax_congr_red                       true
% 10.78/1.98  --pure_diseq_elim                       true
% 10.78/1.98  --brand_transform                       false
% 10.78/1.98  --non_eq_to_eq                          false
% 10.78/1.98  --prep_def_merge                        true
% 10.78/1.98  --prep_def_merge_prop_impl              false
% 10.78/1.98  --prep_def_merge_mbd                    true
% 10.78/1.98  --prep_def_merge_tr_red                 false
% 10.78/1.98  --prep_def_merge_tr_cl                  false
% 10.78/1.98  --smt_preprocessing                     true
% 10.78/1.98  --smt_ac_axioms                         fast
% 10.78/1.98  --preprocessed_out                      false
% 10.78/1.98  --preprocessed_stats                    false
% 10.78/1.98  
% 10.78/1.98  ------ Abstraction refinement Options
% 10.78/1.98  
% 10.78/1.98  --abstr_ref                             []
% 10.78/1.98  --abstr_ref_prep                        false
% 10.78/1.98  --abstr_ref_until_sat                   false
% 10.78/1.98  --abstr_ref_sig_restrict                funpre
% 10.78/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 10.78/1.98  --abstr_ref_under                       []
% 10.78/1.98  
% 10.78/1.98  ------ SAT Options
% 10.78/1.98  
% 10.78/1.98  --sat_mode                              false
% 10.78/1.98  --sat_fm_restart_options                ""
% 10.78/1.98  --sat_gr_def                            false
% 10.78/1.98  --sat_epr_types                         true
% 10.78/1.98  --sat_non_cyclic_types                  false
% 10.78/1.98  --sat_finite_models                     false
% 10.78/1.98  --sat_fm_lemmas                         false
% 10.78/1.98  --sat_fm_prep                           false
% 10.78/1.98  --sat_fm_uc_incr                        true
% 10.78/1.98  --sat_out_model                         small
% 10.78/1.98  --sat_out_clauses                       false
% 10.78/1.98  
% 10.78/1.98  ------ QBF Options
% 10.78/1.98  
% 10.78/1.98  --qbf_mode                              false
% 10.78/1.98  --qbf_elim_univ                         false
% 10.78/1.98  --qbf_dom_inst                          none
% 10.78/1.98  --qbf_dom_pre_inst                      false
% 10.78/1.98  --qbf_sk_in                             false
% 10.78/1.98  --qbf_pred_elim                         true
% 10.78/1.98  --qbf_split                             512
% 10.78/1.98  
% 10.78/1.98  ------ BMC1 Options
% 10.78/1.98  
% 10.78/1.98  --bmc1_incremental                      false
% 10.78/1.98  --bmc1_axioms                           reachable_all
% 10.78/1.98  --bmc1_min_bound                        0
% 10.78/1.98  --bmc1_max_bound                        -1
% 10.78/1.98  --bmc1_max_bound_default                -1
% 10.78/1.98  --bmc1_symbol_reachability              true
% 10.78/1.98  --bmc1_property_lemmas                  false
% 10.78/1.98  --bmc1_k_induction                      false
% 10.78/1.98  --bmc1_non_equiv_states                 false
% 10.78/1.98  --bmc1_deadlock                         false
% 10.78/1.98  --bmc1_ucm                              false
% 10.78/1.98  --bmc1_add_unsat_core                   none
% 10.78/1.98  --bmc1_unsat_core_children              false
% 10.78/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 10.78/1.98  --bmc1_out_stat                         full
% 10.78/1.98  --bmc1_ground_init                      false
% 10.78/1.98  --bmc1_pre_inst_next_state              false
% 10.78/1.98  --bmc1_pre_inst_state                   false
% 10.78/1.98  --bmc1_pre_inst_reach_state             false
% 10.78/1.98  --bmc1_out_unsat_core                   false
% 10.78/1.98  --bmc1_aig_witness_out                  false
% 10.78/1.98  --bmc1_verbose                          false
% 10.78/1.98  --bmc1_dump_clauses_tptp                false
% 10.78/1.98  --bmc1_dump_unsat_core_tptp             false
% 10.78/1.98  --bmc1_dump_file                        -
% 10.78/1.98  --bmc1_ucm_expand_uc_limit              128
% 10.78/1.98  --bmc1_ucm_n_expand_iterations          6
% 10.78/1.98  --bmc1_ucm_extend_mode                  1
% 10.78/1.98  --bmc1_ucm_init_mode                    2
% 10.78/1.98  --bmc1_ucm_cone_mode                    none
% 10.78/1.98  --bmc1_ucm_reduced_relation_type        0
% 10.78/1.98  --bmc1_ucm_relax_model                  4
% 10.78/1.98  --bmc1_ucm_full_tr_after_sat            true
% 10.78/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 10.78/1.98  --bmc1_ucm_layered_model                none
% 10.78/1.98  --bmc1_ucm_max_lemma_size               10
% 10.78/1.98  
% 10.78/1.98  ------ AIG Options
% 10.78/1.98  
% 10.78/1.98  --aig_mode                              false
% 10.78/1.98  
% 10.78/1.98  ------ Instantiation Options
% 10.78/1.98  
% 10.78/1.98  --instantiation_flag                    true
% 10.78/1.98  --inst_sos_flag                         false
% 10.78/1.98  --inst_sos_phase                        true
% 10.78/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 10.78/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 10.78/1.98  --inst_lit_sel_side                     num_symb
% 10.78/1.98  --inst_solver_per_active                1400
% 10.78/1.98  --inst_solver_calls_frac                1.
% 10.78/1.98  --inst_passive_queue_type               priority_queues
% 10.78/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 10.78/1.98  --inst_passive_queues_freq              [25;2]
% 10.78/1.98  --inst_dismatching                      true
% 10.78/1.98  --inst_eager_unprocessed_to_passive     true
% 10.78/1.98  --inst_prop_sim_given                   true
% 10.78/1.98  --inst_prop_sim_new                     false
% 10.78/1.98  --inst_subs_new                         false
% 10.78/1.98  --inst_eq_res_simp                      false
% 10.78/1.98  --inst_subs_given                       false
% 10.78/1.98  --inst_orphan_elimination               true
% 10.78/1.98  --inst_learning_loop_flag               true
% 10.78/1.98  --inst_learning_start                   3000
% 10.78/1.98  --inst_learning_factor                  2
% 10.78/1.98  --inst_start_prop_sim_after_learn       3
% 10.78/1.98  --inst_sel_renew                        solver
% 10.78/1.98  --inst_lit_activity_flag                true
% 10.78/1.98  --inst_restr_to_given                   false
% 10.78/1.98  --inst_activity_threshold               500
% 10.78/1.98  --inst_out_proof                        true
% 10.78/1.98  
% 10.78/1.98  ------ Resolution Options
% 10.78/1.98  
% 10.78/1.98  --resolution_flag                       true
% 10.78/1.98  --res_lit_sel                           adaptive
% 10.78/1.98  --res_lit_sel_side                      none
% 10.78/1.98  --res_ordering                          kbo
% 10.78/1.98  --res_to_prop_solver                    active
% 10.78/1.98  --res_prop_simpl_new                    false
% 10.78/1.98  --res_prop_simpl_given                  true
% 10.78/1.98  --res_passive_queue_type                priority_queues
% 10.78/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 10.78/1.98  --res_passive_queues_freq               [15;5]
% 10.78/1.98  --res_forward_subs                      full
% 10.78/1.98  --res_backward_subs                     full
% 10.78/1.98  --res_forward_subs_resolution           true
% 10.78/1.98  --res_backward_subs_resolution          true
% 10.78/1.98  --res_orphan_elimination                true
% 10.78/1.98  --res_time_limit                        2.
% 10.78/1.98  --res_out_proof                         true
% 10.78/1.98  
% 10.78/1.98  ------ Superposition Options
% 10.78/1.98  
% 10.78/1.98  --superposition_flag                    true
% 10.78/1.98  --sup_passive_queue_type                priority_queues
% 10.78/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 10.78/1.98  --sup_passive_queues_freq               [8;1;4]
% 10.78/1.98  --demod_completeness_check              fast
% 10.78/1.98  --demod_use_ground                      true
% 10.78/1.98  --sup_to_prop_solver                    passive
% 10.78/1.98  --sup_prop_simpl_new                    true
% 10.78/1.98  --sup_prop_simpl_given                  true
% 10.78/1.98  --sup_fun_splitting                     false
% 10.78/1.98  --sup_smt_interval                      50000
% 10.78/1.98  
% 10.78/1.98  ------ Superposition Simplification Setup
% 10.78/1.98  
% 10.78/1.98  --sup_indices_passive                   []
% 10.78/1.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 10.78/1.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 10.78/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 10.78/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 10.78/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 10.78/1.98  --sup_full_bw                           [BwDemod]
% 10.78/1.98  --sup_immed_triv                        [TrivRules]
% 10.78/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 10.78/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 10.78/1.98  --sup_immed_bw_main                     []
% 10.78/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 10.78/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 10.78/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 10.78/1.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 10.78/1.98  
% 10.78/1.98  ------ Combination Options
% 10.78/1.98  
% 10.78/1.98  --comb_res_mult                         3
% 10.78/1.98  --comb_sup_mult                         2
% 10.78/1.98  --comb_inst_mult                        10
% 10.78/1.98  
% 10.78/1.98  ------ Debug Options
% 10.78/1.98  
% 10.78/1.98  --dbg_backtrace                         false
% 10.78/1.98  --dbg_dump_prop_clauses                 false
% 10.78/1.98  --dbg_dump_prop_clauses_file            -
% 10.78/1.98  --dbg_out_stat                          false
% 10.78/1.98  ------ Parsing...
% 10.78/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 10.78/1.98  
% 10.78/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 10.78/1.98  
% 10.78/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 10.78/1.98  
% 10.78/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 10.78/1.98  ------ Proving...
% 10.78/1.98  ------ Problem Properties 
% 10.78/1.98  
% 10.78/1.98  
% 10.78/1.98  clauses                                 10
% 10.78/1.98  conjectures                             3
% 10.78/1.98  EPR                                     0
% 10.78/1.98  Horn                                    10
% 10.78/1.98  unary                                   7
% 10.78/1.98  binary                                  2
% 10.78/1.98  lits                                    14
% 10.78/1.98  lits eq                                 4
% 10.78/1.98  fd_pure                                 0
% 10.78/1.98  fd_pseudo                               0
% 10.78/1.98  fd_cond                                 0
% 10.78/1.98  fd_pseudo_cond                          0
% 10.78/1.98  AC symbols                              0
% 10.78/1.98  
% 10.78/1.98  ------ Schedule dynamic 5 is on 
% 10.78/1.98  
% 10.78/1.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 10.78/1.98  
% 10.78/1.98  
% 10.78/1.98  ------ 
% 10.78/1.98  Current options:
% 10.78/1.98  ------ 
% 10.78/1.98  
% 10.78/1.98  ------ Input Options
% 10.78/1.98  
% 10.78/1.98  --out_options                           all
% 10.78/1.98  --tptp_safe_out                         true
% 10.78/1.98  --problem_path                          ""
% 10.78/1.98  --include_path                          ""
% 10.78/1.98  --clausifier                            res/vclausify_rel
% 10.78/1.98  --clausifier_options                    --mode clausify
% 10.78/1.98  --stdin                                 false
% 10.78/1.98  --stats_out                             all
% 10.78/1.98  
% 10.78/1.98  ------ General Options
% 10.78/1.98  
% 10.78/1.98  --fof                                   false
% 10.78/1.98  --time_out_real                         305.
% 10.78/1.98  --time_out_virtual                      -1.
% 10.78/1.98  --symbol_type_check                     false
% 10.78/1.98  --clausify_out                          false
% 10.78/1.98  --sig_cnt_out                           false
% 10.78/1.98  --trig_cnt_out                          false
% 10.78/1.98  --trig_cnt_out_tolerance                1.
% 10.78/1.98  --trig_cnt_out_sk_spl                   false
% 10.78/1.98  --abstr_cl_out                          false
% 10.78/1.98  
% 10.78/1.98  ------ Global Options
% 10.78/1.98  
% 10.78/1.98  --schedule                              default
% 10.78/1.98  --add_important_lit                     false
% 10.78/1.98  --prop_solver_per_cl                    1000
% 10.78/1.98  --min_unsat_core                        false
% 10.78/1.98  --soft_assumptions                      false
% 10.78/1.98  --soft_lemma_size                       3
% 10.78/1.98  --prop_impl_unit_size                   0
% 10.78/1.98  --prop_impl_unit                        []
% 10.78/1.98  --share_sel_clauses                     true
% 10.78/1.98  --reset_solvers                         false
% 10.78/1.98  --bc_imp_inh                            [conj_cone]
% 10.78/1.98  --conj_cone_tolerance                   3.
% 10.78/1.98  --extra_neg_conj                        none
% 10.78/1.98  --large_theory_mode                     true
% 10.78/1.98  --prolific_symb_bound                   200
% 10.78/1.98  --lt_threshold                          2000
% 10.78/1.98  --clause_weak_htbl                      true
% 10.78/1.98  --gc_record_bc_elim                     false
% 10.78/1.98  
% 10.78/1.98  ------ Preprocessing Options
% 10.78/1.98  
% 10.78/1.98  --preprocessing_flag                    true
% 10.78/1.98  --time_out_prep_mult                    0.1
% 10.78/1.98  --splitting_mode                        input
% 10.78/1.98  --splitting_grd                         true
% 10.78/1.98  --splitting_cvd                         false
% 10.78/1.98  --splitting_cvd_svl                     false
% 10.78/1.98  --splitting_nvd                         32
% 10.78/1.98  --sub_typing                            true
% 10.78/1.98  --prep_gs_sim                           true
% 10.78/1.98  --prep_unflatten                        true
% 10.78/1.98  --prep_res_sim                          true
% 10.78/1.98  --prep_upred                            true
% 10.78/1.98  --prep_sem_filter                       exhaustive
% 10.78/1.98  --prep_sem_filter_out                   false
% 10.78/1.98  --pred_elim                             true
% 10.78/1.98  --res_sim_input                         true
% 10.78/1.98  --eq_ax_congr_red                       true
% 10.78/1.98  --pure_diseq_elim                       true
% 10.78/1.98  --brand_transform                       false
% 10.78/1.98  --non_eq_to_eq                          false
% 10.78/1.98  --prep_def_merge                        true
% 10.78/1.98  --prep_def_merge_prop_impl              false
% 10.78/1.98  --prep_def_merge_mbd                    true
% 10.78/1.98  --prep_def_merge_tr_red                 false
% 10.78/1.98  --prep_def_merge_tr_cl                  false
% 10.78/1.98  --smt_preprocessing                     true
% 10.78/1.98  --smt_ac_axioms                         fast
% 10.78/1.98  --preprocessed_out                      false
% 10.78/1.98  --preprocessed_stats                    false
% 10.78/1.98  
% 10.78/1.98  ------ Abstraction refinement Options
% 10.78/1.98  
% 10.78/1.98  --abstr_ref                             []
% 10.78/1.98  --abstr_ref_prep                        false
% 10.78/1.98  --abstr_ref_until_sat                   false
% 10.78/1.98  --abstr_ref_sig_restrict                funpre
% 10.78/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 10.78/1.98  --abstr_ref_under                       []
% 10.78/1.98  
% 10.78/1.98  ------ SAT Options
% 10.78/1.98  
% 10.78/1.98  --sat_mode                              false
% 10.78/1.98  --sat_fm_restart_options                ""
% 10.78/1.98  --sat_gr_def                            false
% 10.78/1.98  --sat_epr_types                         true
% 10.78/1.98  --sat_non_cyclic_types                  false
% 10.78/1.98  --sat_finite_models                     false
% 10.78/1.98  --sat_fm_lemmas                         false
% 10.78/1.98  --sat_fm_prep                           false
% 10.78/1.98  --sat_fm_uc_incr                        true
% 10.78/1.98  --sat_out_model                         small
% 10.78/1.98  --sat_out_clauses                       false
% 10.78/1.98  
% 10.78/1.98  ------ QBF Options
% 10.78/1.98  
% 10.78/1.98  --qbf_mode                              false
% 10.78/1.98  --qbf_elim_univ                         false
% 10.78/1.98  --qbf_dom_inst                          none
% 10.78/1.98  --qbf_dom_pre_inst                      false
% 10.78/1.98  --qbf_sk_in                             false
% 10.78/1.98  --qbf_pred_elim                         true
% 10.78/1.98  --qbf_split                             512
% 10.78/1.98  
% 10.78/1.98  ------ BMC1 Options
% 10.78/1.98  
% 10.78/1.98  --bmc1_incremental                      false
% 10.78/1.98  --bmc1_axioms                           reachable_all
% 10.78/1.98  --bmc1_min_bound                        0
% 10.78/1.98  --bmc1_max_bound                        -1
% 10.78/1.98  --bmc1_max_bound_default                -1
% 10.78/1.98  --bmc1_symbol_reachability              true
% 10.78/1.98  --bmc1_property_lemmas                  false
% 10.78/1.98  --bmc1_k_induction                      false
% 10.78/1.98  --bmc1_non_equiv_states                 false
% 10.78/1.98  --bmc1_deadlock                         false
% 10.78/1.98  --bmc1_ucm                              false
% 10.78/1.98  --bmc1_add_unsat_core                   none
% 10.78/1.98  --bmc1_unsat_core_children              false
% 10.78/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 10.78/1.98  --bmc1_out_stat                         full
% 10.78/1.98  --bmc1_ground_init                      false
% 10.78/1.98  --bmc1_pre_inst_next_state              false
% 10.78/1.98  --bmc1_pre_inst_state                   false
% 10.78/1.98  --bmc1_pre_inst_reach_state             false
% 10.78/1.98  --bmc1_out_unsat_core                   false
% 10.78/1.98  --bmc1_aig_witness_out                  false
% 10.78/1.98  --bmc1_verbose                          false
% 10.78/1.98  --bmc1_dump_clauses_tptp                false
% 10.78/1.98  --bmc1_dump_unsat_core_tptp             false
% 10.78/1.98  --bmc1_dump_file                        -
% 10.78/1.98  --bmc1_ucm_expand_uc_limit              128
% 10.78/1.98  --bmc1_ucm_n_expand_iterations          6
% 10.78/1.98  --bmc1_ucm_extend_mode                  1
% 10.78/1.98  --bmc1_ucm_init_mode                    2
% 10.78/1.98  --bmc1_ucm_cone_mode                    none
% 10.78/1.98  --bmc1_ucm_reduced_relation_type        0
% 10.78/1.98  --bmc1_ucm_relax_model                  4
% 10.78/1.98  --bmc1_ucm_full_tr_after_sat            true
% 10.78/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 10.78/1.98  --bmc1_ucm_layered_model                none
% 10.78/1.98  --bmc1_ucm_max_lemma_size               10
% 10.78/1.98  
% 10.78/1.98  ------ AIG Options
% 10.78/1.98  
% 10.78/1.98  --aig_mode                              false
% 10.78/1.98  
% 10.78/1.98  ------ Instantiation Options
% 10.78/1.98  
% 10.78/1.98  --instantiation_flag                    true
% 10.78/1.98  --inst_sos_flag                         false
% 10.78/1.98  --inst_sos_phase                        true
% 10.78/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 10.78/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 10.78/1.98  --inst_lit_sel_side                     none
% 10.78/1.98  --inst_solver_per_active                1400
% 10.78/1.98  --inst_solver_calls_frac                1.
% 10.78/1.98  --inst_passive_queue_type               priority_queues
% 10.78/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 10.78/1.98  --inst_passive_queues_freq              [25;2]
% 10.78/1.98  --inst_dismatching                      true
% 10.78/1.98  --inst_eager_unprocessed_to_passive     true
% 10.78/1.98  --inst_prop_sim_given                   true
% 10.78/1.98  --inst_prop_sim_new                     false
% 10.78/1.98  --inst_subs_new                         false
% 10.78/1.98  --inst_eq_res_simp                      false
% 10.78/1.98  --inst_subs_given                       false
% 10.78/1.98  --inst_orphan_elimination               true
% 10.78/1.98  --inst_learning_loop_flag               true
% 10.78/1.98  --inst_learning_start                   3000
% 10.78/1.98  --inst_learning_factor                  2
% 10.78/1.98  --inst_start_prop_sim_after_learn       3
% 10.78/1.98  --inst_sel_renew                        solver
% 10.78/1.98  --inst_lit_activity_flag                true
% 10.78/1.98  --inst_restr_to_given                   false
% 10.78/1.98  --inst_activity_threshold               500
% 10.78/1.98  --inst_out_proof                        true
% 10.78/1.98  
% 10.78/1.98  ------ Resolution Options
% 10.78/1.98  
% 10.78/1.98  --resolution_flag                       false
% 10.78/1.98  --res_lit_sel                           adaptive
% 10.78/1.98  --res_lit_sel_side                      none
% 10.78/1.98  --res_ordering                          kbo
% 10.78/1.98  --res_to_prop_solver                    active
% 10.78/1.98  --res_prop_simpl_new                    false
% 10.78/1.98  --res_prop_simpl_given                  true
% 10.78/1.98  --res_passive_queue_type                priority_queues
% 10.78/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 10.78/1.98  --res_passive_queues_freq               [15;5]
% 10.78/1.98  --res_forward_subs                      full
% 10.78/1.98  --res_backward_subs                     full
% 10.78/1.98  --res_forward_subs_resolution           true
% 10.78/1.98  --res_backward_subs_resolution          true
% 10.78/1.98  --res_orphan_elimination                true
% 10.78/1.98  --res_time_limit                        2.
% 10.78/1.98  --res_out_proof                         true
% 10.78/1.98  
% 10.78/1.98  ------ Superposition Options
% 10.78/1.98  
% 10.78/1.98  --superposition_flag                    true
% 10.78/1.98  --sup_passive_queue_type                priority_queues
% 10.78/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 10.78/1.98  --sup_passive_queues_freq               [8;1;4]
% 10.78/1.98  --demod_completeness_check              fast
% 10.78/1.98  --demod_use_ground                      true
% 10.78/1.98  --sup_to_prop_solver                    passive
% 10.78/1.98  --sup_prop_simpl_new                    true
% 10.78/1.98  --sup_prop_simpl_given                  true
% 10.78/1.98  --sup_fun_splitting                     false
% 10.78/1.98  --sup_smt_interval                      50000
% 10.78/1.98  
% 10.78/1.98  ------ Superposition Simplification Setup
% 10.78/1.98  
% 10.78/1.98  --sup_indices_passive                   []
% 10.78/1.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 10.78/1.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 10.78/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 10.78/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 10.78/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 10.78/1.98  --sup_full_bw                           [BwDemod]
% 10.78/1.98  --sup_immed_triv                        [TrivRules]
% 10.78/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 10.78/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 10.78/1.98  --sup_immed_bw_main                     []
% 10.78/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 10.78/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 10.78/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 10.78/1.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 10.78/1.98  
% 10.78/1.98  ------ Combination Options
% 10.78/1.98  
% 10.78/1.98  --comb_res_mult                         3
% 10.78/1.98  --comb_sup_mult                         2
% 10.78/1.98  --comb_inst_mult                        10
% 10.78/1.98  
% 10.78/1.98  ------ Debug Options
% 10.78/1.98  
% 10.78/1.98  --dbg_backtrace                         false
% 10.78/1.98  --dbg_dump_prop_clauses                 false
% 10.78/1.98  --dbg_dump_prop_clauses_file            -
% 10.78/1.98  --dbg_out_stat                          false
% 10.78/1.98  
% 10.78/1.98  
% 10.78/1.98  
% 10.78/1.98  
% 10.78/1.98  ------ Proving...
% 10.78/1.98  
% 10.78/1.98  
% 10.78/1.98  % SZS status Theorem for theBenchmark.p
% 10.78/1.98  
% 10.78/1.98   Resolution empty clause
% 10.78/1.98  
% 10.78/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 10.78/1.98  
% 10.78/1.98  fof(f7,axiom,(
% 10.78/1.98    ! [X0,X1,X2] : (k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) & k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2))),
% 10.78/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.78/1.98  
% 10.78/1.98  fof(f25,plain,(
% 10.78/1.98    ( ! [X2,X0,X1] : (k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1))) )),
% 10.78/1.98    inference(cnf_transformation,[],[f7])).
% 10.78/1.98  
% 10.78/1.98  fof(f6,axiom,(
% 10.78/1.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 10.78/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.78/1.98  
% 10.78/1.98  fof(f23,plain,(
% 10.78/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 10.78/1.98    inference(cnf_transformation,[],[f6])).
% 10.78/1.98  
% 10.78/1.98  fof(f34,plain,(
% 10.78/1.98    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(X2,k3_tarski(k2_tarski(X0,X1)))) )),
% 10.78/1.98    inference(definition_unfolding,[],[f25,f23,f23])).
% 10.78/1.98  
% 10.78/1.98  fof(f4,axiom,(
% 10.78/1.98    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 10.78/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.78/1.98  
% 10.78/1.98  fof(f12,plain,(
% 10.78/1.98    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 10.78/1.98    inference(ennf_transformation,[],[f4])).
% 10.78/1.98  
% 10.78/1.98  fof(f13,plain,(
% 10.78/1.98    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 10.78/1.98    inference(flattening,[],[f12])).
% 10.78/1.98  
% 10.78/1.98  fof(f21,plain,(
% 10.78/1.98    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 10.78/1.98    inference(cnf_transformation,[],[f13])).
% 10.78/1.98  
% 10.78/1.98  fof(f32,plain,(
% 10.78/1.98    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X3))) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 10.78/1.98    inference(definition_unfolding,[],[f21,f23,f23])).
% 10.78/1.98  
% 10.78/1.98  fof(f8,conjecture,(
% 10.78/1.98    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 10.78/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.78/1.98  
% 10.78/1.98  fof(f9,negated_conjecture,(
% 10.78/1.98    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 10.78/1.98    inference(negated_conjecture,[],[f8])).
% 10.78/1.98  
% 10.78/1.98  fof(f14,plain,(
% 10.78/1.98    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 10.78/1.98    inference(ennf_transformation,[],[f9])).
% 10.78/1.98  
% 10.78/1.98  fof(f15,plain,(
% 10.78/1.98    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 10.78/1.98    inference(flattening,[],[f14])).
% 10.78/1.98  
% 10.78/1.98  fof(f16,plain,(
% 10.78/1.98    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 10.78/1.98    introduced(choice_axiom,[])).
% 10.78/1.98  
% 10.78/1.98  fof(f17,plain,(
% 10.78/1.98    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 10.78/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f15,f16])).
% 10.78/1.98  
% 10.78/1.98  fof(f28,plain,(
% 10.78/1.98    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 10.78/1.98    inference(cnf_transformation,[],[f17])).
% 10.78/1.98  
% 10.78/1.98  fof(f36,plain,(
% 10.78/1.98    ~r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))),
% 10.78/1.98    inference(definition_unfolding,[],[f28,f23,f23,f23])).
% 10.78/1.98  
% 10.78/1.98  fof(f24,plain,(
% 10.78/1.98    ( ! [X2,X0,X1] : (k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2)) )),
% 10.78/1.98    inference(cnf_transformation,[],[f7])).
% 10.78/1.98  
% 10.78/1.98  fof(f35,plain,(
% 10.78/1.98    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) = k2_zfmisc_1(k3_tarski(k2_tarski(X0,X1)),X2)) )),
% 10.78/1.98    inference(definition_unfolding,[],[f24,f23,f23])).
% 10.78/1.98  
% 10.78/1.98  fof(f5,axiom,(
% 10.78/1.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 10.78/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.78/1.98  
% 10.78/1.98  fof(f22,plain,(
% 10.78/1.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 10.78/1.98    inference(cnf_transformation,[],[f5])).
% 10.78/1.98  
% 10.78/1.98  fof(f33,plain,(
% 10.78/1.98    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 10.78/1.98    inference(definition_unfolding,[],[f22,f23])).
% 10.78/1.98  
% 10.78/1.98  fof(f26,plain,(
% 10.78/1.98    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 10.78/1.98    inference(cnf_transformation,[],[f17])).
% 10.78/1.98  
% 10.78/1.98  fof(f3,axiom,(
% 10.78/1.98    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 10.78/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.78/1.98  
% 10.78/1.98  fof(f11,plain,(
% 10.78/1.98    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 10.78/1.98    inference(ennf_transformation,[],[f3])).
% 10.78/1.98  
% 10.78/1.98  fof(f20,plain,(
% 10.78/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 10.78/1.98    inference(cnf_transformation,[],[f11])).
% 10.78/1.98  
% 10.78/1.98  fof(f31,plain,(
% 10.78/1.98    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 10.78/1.98    inference(definition_unfolding,[],[f20,f23])).
% 10.78/1.98  
% 10.78/1.98  fof(f2,axiom,(
% 10.78/1.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 10.78/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.78/1.98  
% 10.78/1.98  fof(f10,plain,(
% 10.78/1.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 10.78/1.98    inference(ennf_transformation,[],[f2])).
% 10.78/1.98  
% 10.78/1.98  fof(f19,plain,(
% 10.78/1.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 10.78/1.98    inference(cnf_transformation,[],[f10])).
% 10.78/1.98  
% 10.78/1.98  fof(f30,plain,(
% 10.78/1.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k3_tarski(k2_tarski(X0,X1)),X2)) )),
% 10.78/1.98    inference(definition_unfolding,[],[f19,f23])).
% 10.78/1.98  
% 10.78/1.98  fof(f1,axiom,(
% 10.78/1.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 10.78/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.78/1.98  
% 10.78/1.98  fof(f18,plain,(
% 10.78/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 10.78/1.98    inference(cnf_transformation,[],[f1])).
% 10.78/1.98  
% 10.78/1.98  fof(f29,plain,(
% 10.78/1.98    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0))) )),
% 10.78/1.98    inference(definition_unfolding,[],[f18,f23,f23])).
% 10.78/1.98  
% 10.78/1.98  fof(f27,plain,(
% 10.78/1.98    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 10.78/1.98    inference(cnf_transformation,[],[f17])).
% 10.78/1.98  
% 10.78/1.98  cnf(c_5,plain,
% 10.78/1.98      ( k3_tarski(k2_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))) = k2_zfmisc_1(X0,k3_tarski(k2_tarski(X1,X2))) ),
% 10.78/1.98      inference(cnf_transformation,[],[f34]) ).
% 10.78/1.98  
% 10.78/1.98  cnf(c_3,plain,
% 10.78/1.98      ( ~ r1_tarski(X0,X1)
% 10.78/1.98      | ~ r1_tarski(X2,X3)
% 10.78/1.98      | r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X3))) ),
% 10.78/1.98      inference(cnf_transformation,[],[f32]) ).
% 10.78/1.98  
% 10.78/1.98  cnf(c_218,plain,
% 10.78/1.98      ( r1_tarski(X0,X1) != iProver_top
% 10.78/1.98      | r1_tarski(X2,X3) != iProver_top
% 10.78/1.98      | r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X3))) = iProver_top ),
% 10.78/1.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 10.78/1.98  
% 10.78/1.98  cnf(c_2819,plain,
% 10.78/1.98      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 10.78/1.98      | r1_tarski(X3,k2_zfmisc_1(X1,X4)) != iProver_top
% 10.78/1.98      | r1_tarski(k3_tarski(k2_tarski(X0,X3)),k2_zfmisc_1(X1,k3_tarski(k2_tarski(X2,X4)))) = iProver_top ),
% 10.78/1.98      inference(superposition,[status(thm)],[c_5,c_218]) ).
% 10.78/1.98  
% 10.78/1.98  cnf(c_7,negated_conjecture,
% 10.78/1.98      ( ~ r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) ),
% 10.78/1.98      inference(cnf_transformation,[],[f36]) ).
% 10.78/1.98  
% 10.78/1.98  cnf(c_216,plain,
% 10.78/1.98      ( r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) != iProver_top ),
% 10.78/1.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 10.78/1.98  
% 10.78/1.98  cnf(c_28529,plain,
% 10.78/1.98      ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK5)) != iProver_top
% 10.78/1.98      | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK3)) != iProver_top ),
% 10.78/1.98      inference(superposition,[status(thm)],[c_2819,c_216]) ).
% 10.78/1.98  
% 10.78/1.98  cnf(c_6,plain,
% 10.78/1.98      ( k3_tarski(k2_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(k3_tarski(k2_tarski(X0,X2)),X1) ),
% 10.78/1.98      inference(cnf_transformation,[],[f35]) ).
% 10.78/1.98  
% 10.78/1.98  cnf(c_4,plain,
% 10.78/1.98      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
% 10.78/1.98      inference(cnf_transformation,[],[f33]) ).
% 10.78/1.98  
% 10.78/1.98  cnf(c_217,plain,
% 10.78/1.98      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
% 10.78/1.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 10.78/1.98  
% 10.78/1.98  cnf(c_847,plain,
% 10.78/1.98      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k3_tarski(k2_tarski(X0,X2)),X1)) = iProver_top ),
% 10.78/1.98      inference(superposition,[status(thm)],[c_6,c_217]) ).
% 10.78/1.98  
% 10.78/1.98  cnf(c_9,negated_conjecture,
% 10.78/1.98      ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
% 10.78/1.98      inference(cnf_transformation,[],[f26]) ).
% 10.78/1.98  
% 10.78/1.98  cnf(c_214,plain,
% 10.78/1.98      ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 10.78/1.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 10.78/1.98  
% 10.78/1.98  cnf(c_2,plain,
% 10.78/1.98      ( ~ r1_tarski(X0,X1) | k3_tarski(k2_tarski(X0,X1)) = X1 ),
% 10.78/1.98      inference(cnf_transformation,[],[f31]) ).
% 10.78/1.98  
% 10.78/1.98  cnf(c_219,plain,
% 10.78/1.98      ( k3_tarski(k2_tarski(X0,X1)) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 10.78/1.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 10.78/1.98  
% 10.78/1.98  cnf(c_692,plain,
% 10.78/1.98      ( k3_tarski(k2_tarski(sK0,k2_zfmisc_1(sK2,sK3))) = k2_zfmisc_1(sK2,sK3) ),
% 10.78/1.98      inference(superposition,[status(thm)],[c_214,c_219]) ).
% 10.78/1.98  
% 10.78/1.98  cnf(c_1,plain,
% 10.78/1.98      ( r1_tarski(X0,X1) | ~ r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
% 10.78/1.98      inference(cnf_transformation,[],[f30]) ).
% 10.78/1.98  
% 10.78/1.98  cnf(c_220,plain,
% 10.78/1.98      ( r1_tarski(X0,X1) = iProver_top
% 10.78/1.98      | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) != iProver_top ),
% 10.78/1.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 10.78/1.98  
% 10.78/1.98  cnf(c_4108,plain,
% 10.78/1.98      ( r1_tarski(k2_zfmisc_1(sK2,sK3),X0) != iProver_top
% 10.78/1.98      | r1_tarski(sK0,X0) = iProver_top ),
% 10.78/1.98      inference(superposition,[status(thm)],[c_692,c_220]) ).
% 10.78/1.98  
% 10.78/1.98  cnf(c_4980,plain,
% 10.78/1.98      ( r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,X0)),sK3)) = iProver_top ),
% 10.78/1.98      inference(superposition,[status(thm)],[c_847,c_4108]) ).
% 10.78/1.98  
% 10.78/1.98  cnf(c_0,plain,
% 10.78/1.98      ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
% 10.78/1.98      inference(cnf_transformation,[],[f29]) ).
% 10.78/1.98  
% 10.78/1.98  cnf(c_424,plain,
% 10.78/1.98      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
% 10.78/1.98      inference(superposition,[status(thm)],[c_0,c_217]) ).
% 10.78/1.98  
% 10.78/1.98  cnf(c_848,plain,
% 10.78/1.98      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k3_tarski(k2_tarski(X2,X0)),X1)) = iProver_top ),
% 10.78/1.98      inference(superposition,[status(thm)],[c_6,c_424]) ).
% 10.78/1.98  
% 10.78/1.98  cnf(c_8,negated_conjecture,
% 10.78/1.98      ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
% 10.78/1.98      inference(cnf_transformation,[],[f27]) ).
% 10.78/1.98  
% 10.78/1.98  cnf(c_215,plain,
% 10.78/1.98      ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 10.78/1.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 10.78/1.98  
% 10.78/1.98  cnf(c_691,plain,
% 10.78/1.98      ( k3_tarski(k2_tarski(sK1,k2_zfmisc_1(sK4,sK5))) = k2_zfmisc_1(sK4,sK5) ),
% 10.78/1.98      inference(superposition,[status(thm)],[c_215,c_219]) ).
% 10.78/1.98  
% 10.78/1.98  cnf(c_4107,plain,
% 10.78/1.98      ( r1_tarski(k2_zfmisc_1(sK4,sK5),X0) != iProver_top
% 10.78/1.98      | r1_tarski(sK1,X0) = iProver_top ),
% 10.78/1.98      inference(superposition,[status(thm)],[c_691,c_220]) ).
% 10.78/1.98  
% 10.78/1.98  cnf(c_4914,plain,
% 10.78/1.98      ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(X0,sK4)),sK5)) = iProver_top ),
% 10.78/1.98      inference(superposition,[status(thm)],[c_848,c_4107]) ).
% 10.78/1.98  
% 10.78/1.98  cnf(c_34598,plain,
% 10.78/1.98      ( $false ),
% 10.78/1.98      inference(forward_subsumption_resolution,
% 10.78/1.98                [status(thm)],
% 10.78/1.98                [c_28529,c_4980,c_4914]) ).
% 10.78/1.98  
% 10.78/1.98  
% 10.78/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 10.78/1.98  
% 10.78/1.98  ------                               Statistics
% 10.78/1.98  
% 10.78/1.98  ------ General
% 10.78/1.98  
% 10.78/1.98  abstr_ref_over_cycles:                  0
% 10.78/1.98  abstr_ref_under_cycles:                 0
% 10.78/1.98  gc_basic_clause_elim:                   0
% 10.78/1.98  forced_gc_time:                         0
% 10.78/1.98  parsing_time:                           0.009
% 10.78/1.98  unif_index_cands_time:                  0.
% 10.78/1.98  unif_index_add_time:                    0.
% 10.78/1.98  orderings_time:                         0.
% 10.78/1.98  out_proof_time:                         0.006
% 10.78/1.98  total_time:                             1.063
% 10.78/1.98  num_of_symbols:                         41
% 10.78/1.98  num_of_terms:                           66734
% 10.78/1.98  
% 10.78/1.98  ------ Preprocessing
% 10.78/1.98  
% 10.78/1.98  num_of_splits:                          0
% 10.78/1.98  num_of_split_atoms:                     0
% 10.78/1.98  num_of_reused_defs:                     0
% 10.78/1.98  num_eq_ax_congr_red:                    0
% 10.78/1.98  num_of_sem_filtered_clauses:            1
% 10.78/1.98  num_of_subtypes:                        0
% 10.78/1.98  monotx_restored_types:                  0
% 10.78/1.98  sat_num_of_epr_types:                   0
% 10.78/1.98  sat_num_of_non_cyclic_types:            0
% 10.78/1.98  sat_guarded_non_collapsed_types:        0
% 10.78/1.98  num_pure_diseq_elim:                    0
% 10.78/1.98  simp_replaced_by:                       0
% 10.78/1.98  res_preprocessed:                       43
% 10.78/1.98  prep_upred:                             0
% 10.78/1.98  prep_unflattend:                        0
% 10.78/1.98  smt_new_axioms:                         0
% 10.78/1.98  pred_elim_cands:                        1
% 10.78/1.98  pred_elim:                              0
% 10.78/1.98  pred_elim_cl:                           0
% 10.78/1.98  pred_elim_cycles:                       1
% 10.78/1.98  merged_defs:                            0
% 10.78/1.98  merged_defs_ncl:                        0
% 10.78/1.98  bin_hyper_res:                          0
% 10.78/1.98  prep_cycles:                            3
% 10.78/1.98  pred_elim_time:                         0.
% 10.78/1.98  splitting_time:                         0.
% 10.78/1.98  sem_filter_time:                        0.
% 10.78/1.98  monotx_time:                            0.
% 10.78/1.98  subtype_inf_time:                       0.
% 10.78/1.98  
% 10.78/1.98  ------ Problem properties
% 10.78/1.98  
% 10.78/1.98  clauses:                                10
% 10.78/1.98  conjectures:                            3
% 10.78/1.98  epr:                                    0
% 10.78/1.98  horn:                                   10
% 10.78/1.98  ground:                                 3
% 10.78/1.98  unary:                                  7
% 10.78/1.98  binary:                                 2
% 10.78/1.98  lits:                                   14
% 10.78/1.98  lits_eq:                                4
% 10.78/1.98  fd_pure:                                0
% 10.78/1.98  fd_pseudo:                              0
% 10.78/1.98  fd_cond:                                0
% 10.78/1.98  fd_pseudo_cond:                         0
% 10.78/1.98  ac_symbols:                             0
% 10.78/1.98  
% 10.78/1.98  ------ Propositional Solver
% 10.78/1.98  
% 10.78/1.98  prop_solver_calls:                      25
% 10.78/1.98  prop_fast_solver_calls:                 333
% 10.78/1.98  smt_solver_calls:                       0
% 10.78/1.98  smt_fast_solver_calls:                  0
% 10.78/1.98  prop_num_of_clauses:                    13574
% 10.78/1.98  prop_preprocess_simplified:             7667
% 10.78/1.98  prop_fo_subsumed:                       0
% 10.78/1.98  prop_solver_time:                       0.
% 10.78/1.98  smt_solver_time:                        0.
% 10.78/1.98  smt_fast_solver_time:                   0.
% 10.78/1.98  prop_fast_solver_time:                  0.
% 10.78/1.98  prop_unsat_core_time:                   0.
% 10.78/1.98  
% 10.78/1.98  ------ QBF
% 10.78/1.98  
% 10.78/1.98  qbf_q_res:                              0
% 10.78/1.98  qbf_num_tautologies:                    0
% 10.78/1.98  qbf_prep_cycles:                        0
% 10.78/1.98  
% 10.78/1.98  ------ BMC1
% 10.78/1.98  
% 10.78/1.98  bmc1_current_bound:                     -1
% 10.78/1.98  bmc1_last_solved_bound:                 -1
% 10.78/1.98  bmc1_unsat_core_size:                   -1
% 10.78/1.98  bmc1_unsat_core_parents_size:           -1
% 10.78/1.98  bmc1_merge_next_fun:                    0
% 10.78/1.98  bmc1_unsat_core_clauses_time:           0.
% 10.78/1.98  
% 10.78/1.98  ------ Instantiation
% 10.78/1.98  
% 10.78/1.98  inst_num_of_clauses:                    1197
% 10.78/1.98  inst_num_in_passive:                    377
% 10.78/1.98  inst_num_in_active:                     683
% 10.78/1.98  inst_num_in_unprocessed:                137
% 10.78/1.98  inst_num_of_loops:                      750
% 10.78/1.98  inst_num_of_learning_restarts:          0
% 10.78/1.98  inst_num_moves_active_passive:          65
% 10.78/1.98  inst_lit_activity:                      0
% 10.78/1.98  inst_lit_activity_moves:                1
% 10.78/1.98  inst_num_tautologies:                   0
% 10.78/1.98  inst_num_prop_implied:                  0
% 10.78/1.98  inst_num_existing_simplified:           0
% 10.78/1.98  inst_num_eq_res_simplified:             0
% 10.78/1.98  inst_num_child_elim:                    0
% 10.78/1.98  inst_num_of_dismatching_blockings:      2377
% 10.78/1.98  inst_num_of_non_proper_insts:           1079
% 10.78/1.98  inst_num_of_duplicates:                 0
% 10.78/1.98  inst_inst_num_from_inst_to_res:         0
% 10.78/1.98  inst_dismatching_checking_time:         0.
% 10.78/1.98  
% 10.78/1.98  ------ Resolution
% 10.78/1.98  
% 10.78/1.98  res_num_of_clauses:                     0
% 10.78/1.98  res_num_in_passive:                     0
% 10.78/1.98  res_num_in_active:                      0
% 10.78/1.98  res_num_of_loops:                       46
% 10.78/1.98  res_forward_subset_subsumed:            7
% 10.78/1.98  res_backward_subset_subsumed:           0
% 10.78/1.98  res_forward_subsumed:                   0
% 10.78/1.98  res_backward_subsumed:                  0
% 10.78/1.98  res_forward_subsumption_resolution:     0
% 10.78/1.98  res_backward_subsumption_resolution:    0
% 10.78/1.98  res_clause_to_clause_subsumption:       35966
% 10.78/1.98  res_orphan_elimination:                 0
% 10.78/1.98  res_tautology_del:                      20
% 10.78/1.98  res_num_eq_res_simplified:              0
% 10.78/1.98  res_num_sel_changes:                    0
% 10.78/1.98  res_moves_from_active_to_pass:          0
% 10.78/1.98  
% 10.78/1.98  ------ Superposition
% 10.78/1.98  
% 10.78/1.98  sup_time_total:                         0.
% 10.78/1.98  sup_time_generating:                    0.
% 10.78/1.98  sup_time_sim_full:                      0.
% 10.78/1.98  sup_time_sim_immed:                     0.
% 10.78/1.98  
% 10.78/1.98  sup_num_of_clauses:                     3516
% 10.78/1.98  sup_num_in_active:                      146
% 10.78/1.98  sup_num_in_passive:                     3370
% 10.78/1.98  sup_num_of_loops:                       148
% 10.78/1.98  sup_fw_superposition:                   3671
% 10.78/1.98  sup_bw_superposition:                   3992
% 10.78/1.98  sup_immediate_simplified:               2218
% 10.78/1.98  sup_given_eliminated:                   0
% 10.78/1.98  comparisons_done:                       0
% 10.78/1.98  comparisons_avoided:                    0
% 10.78/1.98  
% 10.78/1.98  ------ Simplifications
% 10.78/1.98  
% 10.78/1.98  
% 10.78/1.98  sim_fw_subset_subsumed:                 2
% 10.78/1.98  sim_bw_subset_subsumed:                 0
% 10.78/1.98  sim_fw_subsumed:                        499
% 10.78/1.98  sim_bw_subsumed:                        6
% 10.78/1.98  sim_fw_subsumption_res:                 2
% 10.78/1.98  sim_bw_subsumption_res:                 0
% 10.78/1.98  sim_tautology_del:                      135
% 10.78/1.98  sim_eq_tautology_del:                   52
% 10.78/1.98  sim_eq_res_simp:                        0
% 10.78/1.98  sim_fw_demodulated:                     1402
% 10.78/1.98  sim_bw_demodulated:                     158
% 10.78/1.98  sim_light_normalised:                   686
% 10.78/1.98  sim_joinable_taut:                      0
% 10.78/1.98  sim_joinable_simp:                      0
% 10.78/1.98  sim_ac_normalised:                      0
% 10.78/1.98  sim_smt_subsumption:                    0
% 10.78/1.98  
%------------------------------------------------------------------------------
