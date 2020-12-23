%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:42 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 130 expanded)
%              Number of clauses        :   41 (  51 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :   13
%              Number of atoms          :  132 ( 290 expanded)
%              Number of equality atoms :   57 (  67 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).

fof(f30,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f28,f23])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f21,f23])).

fof(f31,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_159,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_377,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_159])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_162,plain,
    ( ~ r1_tarski(X0_40,k1_relat_1(X0_39))
    | ~ v1_relat_1(X0_39)
    | k1_relat_1(k7_relat_1(X0_39,X0_40)) = X0_40 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_374,plain,
    ( k1_relat_1(k7_relat_1(X0_39,X0_40)) = X0_40
    | r1_tarski(X0_40,k1_relat_1(X0_39)) != iProver_top
    | v1_relat_1(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_162])).

cnf(c_777,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_377,c_374])).

cnf(c_9,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_211,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
    inference(instantiation,[status(thm)],[c_162])).

cnf(c_949,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_777,c_9,c_8,c_211])).

cnf(c_158,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_378,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_158])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_165,plain,
    ( ~ v1_relat_1(X0_39)
    | v1_relat_1(k7_relat_1(X0_39,X0_40)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_371,plain,
    ( v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(k7_relat_1(X0_39,X0_40)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_165])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_163,plain,
    ( ~ v1_relat_1(X0_39)
    | k10_relat_1(X0_39,k2_relat_1(X0_39)) = k1_relat_1(X0_39) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_373,plain,
    ( k10_relat_1(X0_39,k2_relat_1(X0_39)) = k1_relat_1(X0_39)
    | v1_relat_1(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_163])).

cnf(c_577,plain,
    ( k10_relat_1(k7_relat_1(X0_39,X0_40),k2_relat_1(k7_relat_1(X0_39,X0_40))) = k1_relat_1(k7_relat_1(X0_39,X0_40))
    | v1_relat_1(X0_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_371,c_373])).

cnf(c_1277,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0_40),k2_relat_1(k7_relat_1(sK1,X0_40))) = k1_relat_1(k7_relat_1(sK1,X0_40)) ),
    inference(superposition,[status(thm)],[c_378,c_577])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_164,plain,
    ( ~ v1_relat_1(X0_39)
    | k2_relat_1(k7_relat_1(X0_39,X0_40)) = k9_relat_1(X0_39,X0_40) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_372,plain,
    ( k2_relat_1(k7_relat_1(X0_39,X0_40)) = k9_relat_1(X0_39,X0_40)
    | v1_relat_1(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_164])).

cnf(c_676,plain,
    ( k2_relat_1(k7_relat_1(sK1,X0_40)) = k9_relat_1(sK1,X0_40) ),
    inference(superposition,[status(thm)],[c_378,c_372])).

cnf(c_1284,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0_40),k9_relat_1(sK1,X0_40)) = k1_relat_1(k7_relat_1(sK1,X0_40)) ),
    inference(light_normalisation,[status(thm)],[c_1277,c_676])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k2_tarski(X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_161,plain,
    ( ~ v1_relat_1(X0_39)
    | k1_setfam_1(k2_tarski(X0_40,k10_relat_1(X0_39,X0_41))) = k10_relat_1(k7_relat_1(X0_39,X0_40),X0_41) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_375,plain,
    ( k1_setfam_1(k2_tarski(X0_40,k10_relat_1(X0_39,X0_41))) = k10_relat_1(k7_relat_1(X0_39,X0_40),X0_41)
    | v1_relat_1(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_161])).

cnf(c_691,plain,
    ( k1_setfam_1(k2_tarski(X0_40,k10_relat_1(sK1,X0_41))) = k10_relat_1(k7_relat_1(sK1,X0_40),X0_41) ),
    inference(superposition,[status(thm)],[c_378,c_375])).

cnf(c_1,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_166,plain,
    ( k2_tarski(X0_40,X1_40) = k2_tarski(X1_40,X0_40) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_0,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_167,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0_40,X1_40)),X0_40) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_370,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0_40,X1_40)),X0_40) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_167])).

cnf(c_503,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0_40,X1_40)),X1_40) = iProver_top ),
    inference(superposition,[status(thm)],[c_166,c_370])).

cnf(c_849,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(sK1,X0_40),X0_41),k10_relat_1(sK1,X0_41)) = iProver_top ),
    inference(superposition,[status(thm)],[c_691,c_503])).

cnf(c_1713,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0_40)),k10_relat_1(sK1,k9_relat_1(sK1,X0_40))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1284,c_849])).

cnf(c_10848,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_949,c_1713])).

cnf(c_7,negated_conjecture,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_12,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10848,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:43:10 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  % Running in FOF mode
% 3.36/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.01  
% 3.36/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.36/1.01  
% 3.36/1.01  ------  iProver source info
% 3.36/1.01  
% 3.36/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.36/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.36/1.01  git: non_committed_changes: false
% 3.36/1.01  git: last_make_outside_of_git: false
% 3.36/1.01  
% 3.36/1.01  ------ 
% 3.36/1.01  
% 3.36/1.01  ------ Input Options
% 3.36/1.01  
% 3.36/1.01  --out_options                           all
% 3.36/1.01  --tptp_safe_out                         true
% 3.36/1.01  --problem_path                          ""
% 3.36/1.01  --include_path                          ""
% 3.36/1.01  --clausifier                            res/vclausify_rel
% 3.36/1.01  --clausifier_options                    --mode clausify
% 3.36/1.01  --stdin                                 false
% 3.36/1.01  --stats_out                             all
% 3.36/1.01  
% 3.36/1.01  ------ General Options
% 3.36/1.01  
% 3.36/1.01  --fof                                   false
% 3.36/1.01  --time_out_real                         305.
% 3.36/1.01  --time_out_virtual                      -1.
% 3.36/1.01  --symbol_type_check                     false
% 3.36/1.01  --clausify_out                          false
% 3.36/1.01  --sig_cnt_out                           false
% 3.36/1.01  --trig_cnt_out                          false
% 3.36/1.01  --trig_cnt_out_tolerance                1.
% 3.36/1.01  --trig_cnt_out_sk_spl                   false
% 3.36/1.01  --abstr_cl_out                          false
% 3.36/1.01  
% 3.36/1.01  ------ Global Options
% 3.36/1.01  
% 3.36/1.01  --schedule                              default
% 3.36/1.01  --add_important_lit                     false
% 3.36/1.01  --prop_solver_per_cl                    1000
% 3.36/1.01  --min_unsat_core                        false
% 3.36/1.01  --soft_assumptions                      false
% 3.36/1.01  --soft_lemma_size                       3
% 3.36/1.01  --prop_impl_unit_size                   0
% 3.36/1.01  --prop_impl_unit                        []
% 3.36/1.01  --share_sel_clauses                     true
% 3.36/1.01  --reset_solvers                         false
% 3.36/1.01  --bc_imp_inh                            [conj_cone]
% 3.36/1.01  --conj_cone_tolerance                   3.
% 3.36/1.01  --extra_neg_conj                        none
% 3.36/1.01  --large_theory_mode                     true
% 3.36/1.01  --prolific_symb_bound                   200
% 3.36/1.01  --lt_threshold                          2000
% 3.36/1.01  --clause_weak_htbl                      true
% 3.36/1.01  --gc_record_bc_elim                     false
% 3.36/1.01  
% 3.36/1.01  ------ Preprocessing Options
% 3.36/1.01  
% 3.36/1.01  --preprocessing_flag                    true
% 3.36/1.01  --time_out_prep_mult                    0.1
% 3.36/1.01  --splitting_mode                        input
% 3.36/1.01  --splitting_grd                         true
% 3.36/1.01  --splitting_cvd                         false
% 3.36/1.01  --splitting_cvd_svl                     false
% 3.36/1.01  --splitting_nvd                         32
% 3.36/1.01  --sub_typing                            true
% 3.36/1.01  --prep_gs_sim                           true
% 3.36/1.01  --prep_unflatten                        true
% 3.36/1.01  --prep_res_sim                          true
% 3.36/1.01  --prep_upred                            true
% 3.36/1.01  --prep_sem_filter                       exhaustive
% 3.36/1.01  --prep_sem_filter_out                   false
% 3.36/1.01  --pred_elim                             true
% 3.36/1.01  --res_sim_input                         true
% 3.36/1.01  --eq_ax_congr_red                       true
% 3.36/1.01  --pure_diseq_elim                       true
% 3.36/1.01  --brand_transform                       false
% 3.36/1.01  --non_eq_to_eq                          false
% 3.36/1.01  --prep_def_merge                        true
% 3.36/1.01  --prep_def_merge_prop_impl              false
% 3.36/1.01  --prep_def_merge_mbd                    true
% 3.36/1.01  --prep_def_merge_tr_red                 false
% 3.36/1.01  --prep_def_merge_tr_cl                  false
% 3.36/1.01  --smt_preprocessing                     true
% 3.36/1.01  --smt_ac_axioms                         fast
% 3.36/1.01  --preprocessed_out                      false
% 3.36/1.01  --preprocessed_stats                    false
% 3.36/1.01  
% 3.36/1.01  ------ Abstraction refinement Options
% 3.36/1.01  
% 3.36/1.01  --abstr_ref                             []
% 3.36/1.01  --abstr_ref_prep                        false
% 3.36/1.01  --abstr_ref_until_sat                   false
% 3.36/1.01  --abstr_ref_sig_restrict                funpre
% 3.36/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.36/1.01  --abstr_ref_under                       []
% 3.36/1.01  
% 3.36/1.01  ------ SAT Options
% 3.36/1.01  
% 3.36/1.01  --sat_mode                              false
% 3.36/1.01  --sat_fm_restart_options                ""
% 3.36/1.01  --sat_gr_def                            false
% 3.36/1.01  --sat_epr_types                         true
% 3.36/1.01  --sat_non_cyclic_types                  false
% 3.36/1.01  --sat_finite_models                     false
% 3.36/1.01  --sat_fm_lemmas                         false
% 3.36/1.01  --sat_fm_prep                           false
% 3.36/1.01  --sat_fm_uc_incr                        true
% 3.36/1.01  --sat_out_model                         small
% 3.36/1.01  --sat_out_clauses                       false
% 3.36/1.01  
% 3.36/1.01  ------ QBF Options
% 3.36/1.01  
% 3.36/1.01  --qbf_mode                              false
% 3.36/1.01  --qbf_elim_univ                         false
% 3.36/1.01  --qbf_dom_inst                          none
% 3.36/1.01  --qbf_dom_pre_inst                      false
% 3.36/1.01  --qbf_sk_in                             false
% 3.36/1.01  --qbf_pred_elim                         true
% 3.36/1.01  --qbf_split                             512
% 3.36/1.01  
% 3.36/1.01  ------ BMC1 Options
% 3.36/1.01  
% 3.36/1.01  --bmc1_incremental                      false
% 3.36/1.01  --bmc1_axioms                           reachable_all
% 3.36/1.01  --bmc1_min_bound                        0
% 3.36/1.01  --bmc1_max_bound                        -1
% 3.36/1.01  --bmc1_max_bound_default                -1
% 3.36/1.01  --bmc1_symbol_reachability              true
% 3.36/1.01  --bmc1_property_lemmas                  false
% 3.36/1.01  --bmc1_k_induction                      false
% 3.36/1.01  --bmc1_non_equiv_states                 false
% 3.36/1.01  --bmc1_deadlock                         false
% 3.36/1.01  --bmc1_ucm                              false
% 3.36/1.01  --bmc1_add_unsat_core                   none
% 3.36/1.01  --bmc1_unsat_core_children              false
% 3.36/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.36/1.01  --bmc1_out_stat                         full
% 3.36/1.01  --bmc1_ground_init                      false
% 3.36/1.01  --bmc1_pre_inst_next_state              false
% 3.36/1.01  --bmc1_pre_inst_state                   false
% 3.36/1.01  --bmc1_pre_inst_reach_state             false
% 3.36/1.01  --bmc1_out_unsat_core                   false
% 3.36/1.01  --bmc1_aig_witness_out                  false
% 3.36/1.01  --bmc1_verbose                          false
% 3.36/1.01  --bmc1_dump_clauses_tptp                false
% 3.36/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.36/1.01  --bmc1_dump_file                        -
% 3.36/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.36/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.36/1.01  --bmc1_ucm_extend_mode                  1
% 3.36/1.01  --bmc1_ucm_init_mode                    2
% 3.36/1.01  --bmc1_ucm_cone_mode                    none
% 3.36/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.36/1.01  --bmc1_ucm_relax_model                  4
% 3.36/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.36/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.36/1.01  --bmc1_ucm_layered_model                none
% 3.36/1.01  --bmc1_ucm_max_lemma_size               10
% 3.36/1.01  
% 3.36/1.01  ------ AIG Options
% 3.36/1.01  
% 3.36/1.01  --aig_mode                              false
% 3.36/1.01  
% 3.36/1.01  ------ Instantiation Options
% 3.36/1.01  
% 3.36/1.01  --instantiation_flag                    true
% 3.36/1.01  --inst_sos_flag                         false
% 3.36/1.01  --inst_sos_phase                        true
% 3.36/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.36/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.36/1.01  --inst_lit_sel_side                     num_symb
% 3.36/1.01  --inst_solver_per_active                1400
% 3.36/1.01  --inst_solver_calls_frac                1.
% 3.36/1.01  --inst_passive_queue_type               priority_queues
% 3.36/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.36/1.01  --inst_passive_queues_freq              [25;2]
% 3.36/1.01  --inst_dismatching                      true
% 3.36/1.01  --inst_eager_unprocessed_to_passive     true
% 3.36/1.01  --inst_prop_sim_given                   true
% 3.36/1.01  --inst_prop_sim_new                     false
% 3.36/1.01  --inst_subs_new                         false
% 3.36/1.01  --inst_eq_res_simp                      false
% 3.36/1.01  --inst_subs_given                       false
% 3.36/1.01  --inst_orphan_elimination               true
% 3.36/1.01  --inst_learning_loop_flag               true
% 3.36/1.01  --inst_learning_start                   3000
% 3.36/1.01  --inst_learning_factor                  2
% 3.36/1.01  --inst_start_prop_sim_after_learn       3
% 3.36/1.01  --inst_sel_renew                        solver
% 3.36/1.01  --inst_lit_activity_flag                true
% 3.36/1.01  --inst_restr_to_given                   false
% 3.36/1.01  --inst_activity_threshold               500
% 3.36/1.01  --inst_out_proof                        true
% 3.36/1.01  
% 3.36/1.01  ------ Resolution Options
% 3.36/1.01  
% 3.36/1.01  --resolution_flag                       true
% 3.36/1.01  --res_lit_sel                           adaptive
% 3.36/1.01  --res_lit_sel_side                      none
% 3.36/1.01  --res_ordering                          kbo
% 3.36/1.01  --res_to_prop_solver                    active
% 3.36/1.01  --res_prop_simpl_new                    false
% 3.36/1.01  --res_prop_simpl_given                  true
% 3.36/1.01  --res_passive_queue_type                priority_queues
% 3.36/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.36/1.01  --res_passive_queues_freq               [15;5]
% 3.36/1.01  --res_forward_subs                      full
% 3.36/1.01  --res_backward_subs                     full
% 3.36/1.01  --res_forward_subs_resolution           true
% 3.36/1.01  --res_backward_subs_resolution          true
% 3.36/1.01  --res_orphan_elimination                true
% 3.36/1.01  --res_time_limit                        2.
% 3.36/1.01  --res_out_proof                         true
% 3.36/1.01  
% 3.36/1.01  ------ Superposition Options
% 3.36/1.01  
% 3.36/1.01  --superposition_flag                    true
% 3.36/1.01  --sup_passive_queue_type                priority_queues
% 3.36/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.36/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.36/1.01  --demod_completeness_check              fast
% 3.36/1.01  --demod_use_ground                      true
% 3.36/1.01  --sup_to_prop_solver                    passive
% 3.36/1.01  --sup_prop_simpl_new                    true
% 3.36/1.01  --sup_prop_simpl_given                  true
% 3.36/1.01  --sup_fun_splitting                     false
% 3.36/1.01  --sup_smt_interval                      50000
% 3.36/1.01  
% 3.36/1.01  ------ Superposition Simplification Setup
% 3.36/1.01  
% 3.36/1.01  --sup_indices_passive                   []
% 3.36/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.36/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.01  --sup_full_bw                           [BwDemod]
% 3.36/1.01  --sup_immed_triv                        [TrivRules]
% 3.36/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.36/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.01  --sup_immed_bw_main                     []
% 3.36/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.36/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/1.01  
% 3.36/1.01  ------ Combination Options
% 3.36/1.01  
% 3.36/1.01  --comb_res_mult                         3
% 3.36/1.01  --comb_sup_mult                         2
% 3.36/1.01  --comb_inst_mult                        10
% 3.36/1.01  
% 3.36/1.01  ------ Debug Options
% 3.36/1.01  
% 3.36/1.01  --dbg_backtrace                         false
% 3.36/1.01  --dbg_dump_prop_clauses                 false
% 3.36/1.01  --dbg_dump_prop_clauses_file            -
% 3.36/1.01  --dbg_out_stat                          false
% 3.36/1.01  ------ Parsing...
% 3.36/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.36/1.01  
% 3.36/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.36/1.01  
% 3.36/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.36/1.01  
% 3.36/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.36/1.01  ------ Proving...
% 3.36/1.01  ------ Problem Properties 
% 3.36/1.01  
% 3.36/1.01  
% 3.36/1.01  clauses                                 10
% 3.36/1.01  conjectures                             3
% 3.36/1.01  EPR                                     1
% 3.36/1.01  Horn                                    10
% 3.36/1.01  unary                                   5
% 3.36/1.01  binary                                  4
% 3.36/1.01  lits                                    16
% 3.36/1.01  lits eq                                 5
% 3.36/1.01  fd_pure                                 0
% 3.36/1.01  fd_pseudo                               0
% 3.36/1.01  fd_cond                                 0
% 3.36/1.01  fd_pseudo_cond                          0
% 3.36/1.01  AC symbols                              0
% 3.36/1.01  
% 3.36/1.01  ------ Schedule dynamic 5 is on 
% 3.36/1.01  
% 3.36/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.36/1.01  
% 3.36/1.01  
% 3.36/1.01  ------ 
% 3.36/1.01  Current options:
% 3.36/1.01  ------ 
% 3.36/1.01  
% 3.36/1.01  ------ Input Options
% 3.36/1.01  
% 3.36/1.01  --out_options                           all
% 3.36/1.01  --tptp_safe_out                         true
% 3.36/1.01  --problem_path                          ""
% 3.36/1.01  --include_path                          ""
% 3.36/1.01  --clausifier                            res/vclausify_rel
% 3.36/1.01  --clausifier_options                    --mode clausify
% 3.36/1.01  --stdin                                 false
% 3.36/1.01  --stats_out                             all
% 3.36/1.01  
% 3.36/1.01  ------ General Options
% 3.36/1.01  
% 3.36/1.01  --fof                                   false
% 3.36/1.01  --time_out_real                         305.
% 3.36/1.01  --time_out_virtual                      -1.
% 3.36/1.01  --symbol_type_check                     false
% 3.36/1.01  --clausify_out                          false
% 3.36/1.01  --sig_cnt_out                           false
% 3.36/1.01  --trig_cnt_out                          false
% 3.36/1.01  --trig_cnt_out_tolerance                1.
% 3.36/1.01  --trig_cnt_out_sk_spl                   false
% 3.36/1.01  --abstr_cl_out                          false
% 3.36/1.01  
% 3.36/1.01  ------ Global Options
% 3.36/1.01  
% 3.36/1.01  --schedule                              default
% 3.36/1.01  --add_important_lit                     false
% 3.36/1.01  --prop_solver_per_cl                    1000
% 3.36/1.01  --min_unsat_core                        false
% 3.36/1.01  --soft_assumptions                      false
% 3.36/1.01  --soft_lemma_size                       3
% 3.36/1.01  --prop_impl_unit_size                   0
% 3.36/1.01  --prop_impl_unit                        []
% 3.36/1.01  --share_sel_clauses                     true
% 3.36/1.01  --reset_solvers                         false
% 3.36/1.01  --bc_imp_inh                            [conj_cone]
% 3.36/1.01  --conj_cone_tolerance                   3.
% 3.36/1.01  --extra_neg_conj                        none
% 3.36/1.01  --large_theory_mode                     true
% 3.36/1.01  --prolific_symb_bound                   200
% 3.36/1.01  --lt_threshold                          2000
% 3.36/1.01  --clause_weak_htbl                      true
% 3.36/1.01  --gc_record_bc_elim                     false
% 3.36/1.01  
% 3.36/1.01  ------ Preprocessing Options
% 3.36/1.01  
% 3.36/1.01  --preprocessing_flag                    true
% 3.36/1.01  --time_out_prep_mult                    0.1
% 3.36/1.01  --splitting_mode                        input
% 3.36/1.01  --splitting_grd                         true
% 3.36/1.01  --splitting_cvd                         false
% 3.36/1.01  --splitting_cvd_svl                     false
% 3.36/1.01  --splitting_nvd                         32
% 3.36/1.01  --sub_typing                            true
% 3.36/1.01  --prep_gs_sim                           true
% 3.36/1.01  --prep_unflatten                        true
% 3.36/1.01  --prep_res_sim                          true
% 3.36/1.01  --prep_upred                            true
% 3.36/1.01  --prep_sem_filter                       exhaustive
% 3.36/1.01  --prep_sem_filter_out                   false
% 3.36/1.01  --pred_elim                             true
% 3.36/1.01  --res_sim_input                         true
% 3.36/1.01  --eq_ax_congr_red                       true
% 3.36/1.01  --pure_diseq_elim                       true
% 3.36/1.01  --brand_transform                       false
% 3.36/1.01  --non_eq_to_eq                          false
% 3.36/1.01  --prep_def_merge                        true
% 3.36/1.01  --prep_def_merge_prop_impl              false
% 3.36/1.01  --prep_def_merge_mbd                    true
% 3.36/1.01  --prep_def_merge_tr_red                 false
% 3.36/1.01  --prep_def_merge_tr_cl                  false
% 3.36/1.01  --smt_preprocessing                     true
% 3.36/1.01  --smt_ac_axioms                         fast
% 3.36/1.01  --preprocessed_out                      false
% 3.36/1.01  --preprocessed_stats                    false
% 3.36/1.01  
% 3.36/1.01  ------ Abstraction refinement Options
% 3.36/1.01  
% 3.36/1.01  --abstr_ref                             []
% 3.36/1.01  --abstr_ref_prep                        false
% 3.36/1.01  --abstr_ref_until_sat                   false
% 3.36/1.01  --abstr_ref_sig_restrict                funpre
% 3.36/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.36/1.01  --abstr_ref_under                       []
% 3.36/1.01  
% 3.36/1.01  ------ SAT Options
% 3.36/1.01  
% 3.36/1.01  --sat_mode                              false
% 3.36/1.01  --sat_fm_restart_options                ""
% 3.36/1.01  --sat_gr_def                            false
% 3.36/1.01  --sat_epr_types                         true
% 3.36/1.01  --sat_non_cyclic_types                  false
% 3.36/1.01  --sat_finite_models                     false
% 3.36/1.01  --sat_fm_lemmas                         false
% 3.36/1.01  --sat_fm_prep                           false
% 3.36/1.01  --sat_fm_uc_incr                        true
% 3.36/1.01  --sat_out_model                         small
% 3.36/1.01  --sat_out_clauses                       false
% 3.36/1.01  
% 3.36/1.01  ------ QBF Options
% 3.36/1.01  
% 3.36/1.01  --qbf_mode                              false
% 3.36/1.01  --qbf_elim_univ                         false
% 3.36/1.01  --qbf_dom_inst                          none
% 3.36/1.01  --qbf_dom_pre_inst                      false
% 3.36/1.01  --qbf_sk_in                             false
% 3.36/1.01  --qbf_pred_elim                         true
% 3.36/1.01  --qbf_split                             512
% 3.36/1.01  
% 3.36/1.01  ------ BMC1 Options
% 3.36/1.01  
% 3.36/1.01  --bmc1_incremental                      false
% 3.36/1.01  --bmc1_axioms                           reachable_all
% 3.36/1.01  --bmc1_min_bound                        0
% 3.36/1.01  --bmc1_max_bound                        -1
% 3.36/1.01  --bmc1_max_bound_default                -1
% 3.36/1.01  --bmc1_symbol_reachability              true
% 3.36/1.01  --bmc1_property_lemmas                  false
% 3.36/1.01  --bmc1_k_induction                      false
% 3.36/1.01  --bmc1_non_equiv_states                 false
% 3.36/1.01  --bmc1_deadlock                         false
% 3.36/1.01  --bmc1_ucm                              false
% 3.36/1.01  --bmc1_add_unsat_core                   none
% 3.36/1.01  --bmc1_unsat_core_children              false
% 3.36/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.36/1.01  --bmc1_out_stat                         full
% 3.36/1.01  --bmc1_ground_init                      false
% 3.36/1.01  --bmc1_pre_inst_next_state              false
% 3.36/1.01  --bmc1_pre_inst_state                   false
% 3.36/1.01  --bmc1_pre_inst_reach_state             false
% 3.36/1.01  --bmc1_out_unsat_core                   false
% 3.36/1.01  --bmc1_aig_witness_out                  false
% 3.36/1.01  --bmc1_verbose                          false
% 3.36/1.01  --bmc1_dump_clauses_tptp                false
% 3.36/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.36/1.01  --bmc1_dump_file                        -
% 3.36/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.36/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.36/1.01  --bmc1_ucm_extend_mode                  1
% 3.36/1.01  --bmc1_ucm_init_mode                    2
% 3.36/1.01  --bmc1_ucm_cone_mode                    none
% 3.36/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.36/1.01  --bmc1_ucm_relax_model                  4
% 3.36/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.36/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.36/1.01  --bmc1_ucm_layered_model                none
% 3.36/1.01  --bmc1_ucm_max_lemma_size               10
% 3.36/1.01  
% 3.36/1.01  ------ AIG Options
% 3.36/1.01  
% 3.36/1.01  --aig_mode                              false
% 3.36/1.01  
% 3.36/1.01  ------ Instantiation Options
% 3.36/1.01  
% 3.36/1.01  --instantiation_flag                    true
% 3.36/1.01  --inst_sos_flag                         false
% 3.36/1.01  --inst_sos_phase                        true
% 3.36/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.36/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.36/1.01  --inst_lit_sel_side                     none
% 3.36/1.01  --inst_solver_per_active                1400
% 3.36/1.01  --inst_solver_calls_frac                1.
% 3.36/1.01  --inst_passive_queue_type               priority_queues
% 3.36/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.36/1.01  --inst_passive_queues_freq              [25;2]
% 3.36/1.01  --inst_dismatching                      true
% 3.36/1.01  --inst_eager_unprocessed_to_passive     true
% 3.36/1.01  --inst_prop_sim_given                   true
% 3.36/1.01  --inst_prop_sim_new                     false
% 3.36/1.01  --inst_subs_new                         false
% 3.36/1.01  --inst_eq_res_simp                      false
% 3.36/1.01  --inst_subs_given                       false
% 3.36/1.01  --inst_orphan_elimination               true
% 3.36/1.01  --inst_learning_loop_flag               true
% 3.36/1.01  --inst_learning_start                   3000
% 3.36/1.01  --inst_learning_factor                  2
% 3.36/1.01  --inst_start_prop_sim_after_learn       3
% 3.36/1.01  --inst_sel_renew                        solver
% 3.36/1.01  --inst_lit_activity_flag                true
% 3.36/1.01  --inst_restr_to_given                   false
% 3.36/1.01  --inst_activity_threshold               500
% 3.36/1.01  --inst_out_proof                        true
% 3.36/1.01  
% 3.36/1.01  ------ Resolution Options
% 3.36/1.01  
% 3.36/1.01  --resolution_flag                       false
% 3.36/1.01  --res_lit_sel                           adaptive
% 3.36/1.01  --res_lit_sel_side                      none
% 3.36/1.01  --res_ordering                          kbo
% 3.36/1.01  --res_to_prop_solver                    active
% 3.36/1.01  --res_prop_simpl_new                    false
% 3.36/1.01  --res_prop_simpl_given                  true
% 3.36/1.01  --res_passive_queue_type                priority_queues
% 3.36/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.36/1.01  --res_passive_queues_freq               [15;5]
% 3.36/1.01  --res_forward_subs                      full
% 3.36/1.01  --res_backward_subs                     full
% 3.36/1.01  --res_forward_subs_resolution           true
% 3.36/1.01  --res_backward_subs_resolution          true
% 3.36/1.01  --res_orphan_elimination                true
% 3.36/1.01  --res_time_limit                        2.
% 3.36/1.01  --res_out_proof                         true
% 3.36/1.01  
% 3.36/1.01  ------ Superposition Options
% 3.36/1.01  
% 3.36/1.01  --superposition_flag                    true
% 3.36/1.01  --sup_passive_queue_type                priority_queues
% 3.36/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.36/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.36/1.01  --demod_completeness_check              fast
% 3.36/1.01  --demod_use_ground                      true
% 3.36/1.01  --sup_to_prop_solver                    passive
% 3.36/1.01  --sup_prop_simpl_new                    true
% 3.36/1.01  --sup_prop_simpl_given                  true
% 3.36/1.01  --sup_fun_splitting                     false
% 3.36/1.01  --sup_smt_interval                      50000
% 3.36/1.01  
% 3.36/1.01  ------ Superposition Simplification Setup
% 3.36/1.01  
% 3.36/1.01  --sup_indices_passive                   []
% 3.36/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.36/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.01  --sup_full_bw                           [BwDemod]
% 3.36/1.01  --sup_immed_triv                        [TrivRules]
% 3.36/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.36/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.01  --sup_immed_bw_main                     []
% 3.36/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.36/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/1.01  
% 3.36/1.01  ------ Combination Options
% 3.36/1.01  
% 3.36/1.01  --comb_res_mult                         3
% 3.36/1.01  --comb_sup_mult                         2
% 3.36/1.01  --comb_inst_mult                        10
% 3.36/1.01  
% 3.36/1.01  ------ Debug Options
% 3.36/1.01  
% 3.36/1.01  --dbg_backtrace                         false
% 3.36/1.01  --dbg_dump_prop_clauses                 false
% 3.36/1.01  --dbg_dump_prop_clauses_file            -
% 3.36/1.01  --dbg_out_stat                          false
% 3.36/1.01  
% 3.36/1.01  
% 3.36/1.01  
% 3.36/1.01  
% 3.36/1.01  ------ Proving...
% 3.36/1.01  
% 3.36/1.01  
% 3.36/1.01  % SZS status Theorem for theBenchmark.p
% 3.36/1.01  
% 3.36/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.36/1.01  
% 3.36/1.01  fof(f9,conjecture,(
% 3.36/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 3.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.01  
% 3.36/1.01  fof(f10,negated_conjecture,(
% 3.36/1.01    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 3.36/1.01    inference(negated_conjecture,[],[f9])).
% 3.36/1.01  
% 3.36/1.01  fof(f17,plain,(
% 3.36/1.01    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 3.36/1.01    inference(ennf_transformation,[],[f10])).
% 3.36/1.01  
% 3.36/1.01  fof(f18,plain,(
% 3.36/1.01    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 3.36/1.01    inference(flattening,[],[f17])).
% 3.36/1.01  
% 3.36/1.01  fof(f19,plain,(
% 3.36/1.01    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 3.36/1.01    introduced(choice_axiom,[])).
% 3.36/1.01  
% 3.36/1.01  fof(f20,plain,(
% 3.36/1.01    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 3.36/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).
% 3.36/1.01  
% 3.36/1.01  fof(f30,plain,(
% 3.36/1.01    r1_tarski(sK0,k1_relat_1(sK1))),
% 3.36/1.01    inference(cnf_transformation,[],[f20])).
% 3.36/1.01  
% 3.36/1.01  fof(f7,axiom,(
% 3.36/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.01  
% 3.36/1.01  fof(f14,plain,(
% 3.36/1.01    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.36/1.01    inference(ennf_transformation,[],[f7])).
% 3.36/1.01  
% 3.36/1.01  fof(f15,plain,(
% 3.36/1.01    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.36/1.01    inference(flattening,[],[f14])).
% 3.36/1.01  
% 3.36/1.01  fof(f27,plain,(
% 3.36/1.01    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.36/1.01    inference(cnf_transformation,[],[f15])).
% 3.36/1.01  
% 3.36/1.01  fof(f29,plain,(
% 3.36/1.01    v1_relat_1(sK1)),
% 3.36/1.01    inference(cnf_transformation,[],[f20])).
% 3.36/1.01  
% 3.36/1.01  fof(f4,axiom,(
% 3.36/1.01    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.01  
% 3.36/1.01  fof(f11,plain,(
% 3.36/1.01    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.36/1.01    inference(ennf_transformation,[],[f4])).
% 3.36/1.01  
% 3.36/1.01  fof(f24,plain,(
% 3.36/1.01    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.36/1.01    inference(cnf_transformation,[],[f11])).
% 3.36/1.01  
% 3.36/1.01  fof(f6,axiom,(
% 3.36/1.01    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 3.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.01  
% 3.36/1.01  fof(f13,plain,(
% 3.36/1.01    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 3.36/1.01    inference(ennf_transformation,[],[f6])).
% 3.36/1.01  
% 3.36/1.01  fof(f26,plain,(
% 3.36/1.01    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.36/1.01    inference(cnf_transformation,[],[f13])).
% 3.36/1.01  
% 3.36/1.01  fof(f5,axiom,(
% 3.36/1.01    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.01  
% 3.36/1.01  fof(f12,plain,(
% 3.36/1.01    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.36/1.01    inference(ennf_transformation,[],[f5])).
% 3.36/1.01  
% 3.36/1.01  fof(f25,plain,(
% 3.36/1.01    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.36/1.01    inference(cnf_transformation,[],[f12])).
% 3.36/1.01  
% 3.36/1.01  fof(f8,axiom,(
% 3.36/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 3.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.01  
% 3.36/1.01  fof(f16,plain,(
% 3.36/1.01    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 3.36/1.01    inference(ennf_transformation,[],[f8])).
% 3.36/1.01  
% 3.36/1.01  fof(f28,plain,(
% 3.36/1.01    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 3.36/1.01    inference(cnf_transformation,[],[f16])).
% 3.36/1.01  
% 3.36/1.01  fof(f3,axiom,(
% 3.36/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.01  
% 3.36/1.01  fof(f23,plain,(
% 3.36/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.36/1.01    inference(cnf_transformation,[],[f3])).
% 3.36/1.01  
% 3.36/1.01  fof(f33,plain,(
% 3.36/1.01    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 3.36/1.01    inference(definition_unfolding,[],[f28,f23])).
% 3.36/1.01  
% 3.36/1.01  fof(f2,axiom,(
% 3.36/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.01  
% 3.36/1.01  fof(f22,plain,(
% 3.36/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.36/1.01    inference(cnf_transformation,[],[f2])).
% 3.36/1.01  
% 3.36/1.01  fof(f1,axiom,(
% 3.36/1.01    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.36/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.01  
% 3.36/1.01  fof(f21,plain,(
% 3.36/1.01    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.36/1.01    inference(cnf_transformation,[],[f1])).
% 3.36/1.01  
% 3.36/1.01  fof(f32,plain,(
% 3.36/1.01    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 3.36/1.01    inference(definition_unfolding,[],[f21,f23])).
% 3.36/1.01  
% 3.36/1.01  fof(f31,plain,(
% 3.36/1.01    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 3.36/1.01    inference(cnf_transformation,[],[f20])).
% 3.36/1.01  
% 3.36/1.01  cnf(c_8,negated_conjecture,
% 3.36/1.01      ( r1_tarski(sK0,k1_relat_1(sK1)) ),
% 3.36/1.01      inference(cnf_transformation,[],[f30]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_159,negated_conjecture,
% 3.36/1.01      ( r1_tarski(sK0,k1_relat_1(sK1)) ),
% 3.36/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_377,plain,
% 3.36/1.01      ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
% 3.36/1.01      inference(predicate_to_equality,[status(thm)],[c_159]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_5,plain,
% 3.36/1.01      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.36/1.01      | ~ v1_relat_1(X1)
% 3.36/1.01      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.36/1.01      inference(cnf_transformation,[],[f27]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_162,plain,
% 3.36/1.01      ( ~ r1_tarski(X0_40,k1_relat_1(X0_39))
% 3.36/1.01      | ~ v1_relat_1(X0_39)
% 3.36/1.01      | k1_relat_1(k7_relat_1(X0_39,X0_40)) = X0_40 ),
% 3.36/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_374,plain,
% 3.36/1.01      ( k1_relat_1(k7_relat_1(X0_39,X0_40)) = X0_40
% 3.36/1.01      | r1_tarski(X0_40,k1_relat_1(X0_39)) != iProver_top
% 3.36/1.01      | v1_relat_1(X0_39) != iProver_top ),
% 3.36/1.01      inference(predicate_to_equality,[status(thm)],[c_162]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_777,plain,
% 3.36/1.01      ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
% 3.36/1.01      | v1_relat_1(sK1) != iProver_top ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_377,c_374]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_9,negated_conjecture,
% 3.36/1.01      ( v1_relat_1(sK1) ),
% 3.36/1.01      inference(cnf_transformation,[],[f29]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_211,plain,
% 3.36/1.01      ( ~ r1_tarski(sK0,k1_relat_1(sK1))
% 3.36/1.01      | ~ v1_relat_1(sK1)
% 3.36/1.01      | k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
% 3.36/1.01      inference(instantiation,[status(thm)],[c_162]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_949,plain,
% 3.36/1.01      ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
% 3.36/1.01      inference(global_propositional_subsumption,
% 3.36/1.01                [status(thm)],
% 3.36/1.01                [c_777,c_9,c_8,c_211]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_158,negated_conjecture,
% 3.36/1.01      ( v1_relat_1(sK1) ),
% 3.36/1.01      inference(subtyping,[status(esa)],[c_9]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_378,plain,
% 3.36/1.01      ( v1_relat_1(sK1) = iProver_top ),
% 3.36/1.01      inference(predicate_to_equality,[status(thm)],[c_158]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_2,plain,
% 3.36/1.01      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 3.36/1.01      inference(cnf_transformation,[],[f24]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_165,plain,
% 3.36/1.01      ( ~ v1_relat_1(X0_39) | v1_relat_1(k7_relat_1(X0_39,X0_40)) ),
% 3.36/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_371,plain,
% 3.36/1.01      ( v1_relat_1(X0_39) != iProver_top
% 3.36/1.01      | v1_relat_1(k7_relat_1(X0_39,X0_40)) = iProver_top ),
% 3.36/1.01      inference(predicate_to_equality,[status(thm)],[c_165]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_4,plain,
% 3.36/1.01      ( ~ v1_relat_1(X0)
% 3.36/1.01      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 3.36/1.01      inference(cnf_transformation,[],[f26]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_163,plain,
% 3.36/1.01      ( ~ v1_relat_1(X0_39)
% 3.36/1.01      | k10_relat_1(X0_39,k2_relat_1(X0_39)) = k1_relat_1(X0_39) ),
% 3.36/1.01      inference(subtyping,[status(esa)],[c_4]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_373,plain,
% 3.36/1.01      ( k10_relat_1(X0_39,k2_relat_1(X0_39)) = k1_relat_1(X0_39)
% 3.36/1.01      | v1_relat_1(X0_39) != iProver_top ),
% 3.36/1.01      inference(predicate_to_equality,[status(thm)],[c_163]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_577,plain,
% 3.36/1.01      ( k10_relat_1(k7_relat_1(X0_39,X0_40),k2_relat_1(k7_relat_1(X0_39,X0_40))) = k1_relat_1(k7_relat_1(X0_39,X0_40))
% 3.36/1.01      | v1_relat_1(X0_39) != iProver_top ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_371,c_373]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1277,plain,
% 3.36/1.01      ( k10_relat_1(k7_relat_1(sK1,X0_40),k2_relat_1(k7_relat_1(sK1,X0_40))) = k1_relat_1(k7_relat_1(sK1,X0_40)) ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_378,c_577]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_3,plain,
% 3.36/1.01      ( ~ v1_relat_1(X0)
% 3.36/1.01      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.36/1.01      inference(cnf_transformation,[],[f25]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_164,plain,
% 3.36/1.01      ( ~ v1_relat_1(X0_39)
% 3.36/1.01      | k2_relat_1(k7_relat_1(X0_39,X0_40)) = k9_relat_1(X0_39,X0_40) ),
% 3.36/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_372,plain,
% 3.36/1.01      ( k2_relat_1(k7_relat_1(X0_39,X0_40)) = k9_relat_1(X0_39,X0_40)
% 3.36/1.01      | v1_relat_1(X0_39) != iProver_top ),
% 3.36/1.01      inference(predicate_to_equality,[status(thm)],[c_164]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_676,plain,
% 3.36/1.01      ( k2_relat_1(k7_relat_1(sK1,X0_40)) = k9_relat_1(sK1,X0_40) ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_378,c_372]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1284,plain,
% 3.36/1.01      ( k10_relat_1(k7_relat_1(sK1,X0_40),k9_relat_1(sK1,X0_40)) = k1_relat_1(k7_relat_1(sK1,X0_40)) ),
% 3.36/1.01      inference(light_normalisation,[status(thm)],[c_1277,c_676]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_6,plain,
% 3.36/1.01      ( ~ v1_relat_1(X0)
% 3.36/1.01      | k1_setfam_1(k2_tarski(X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 3.36/1.01      inference(cnf_transformation,[],[f33]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_161,plain,
% 3.36/1.01      ( ~ v1_relat_1(X0_39)
% 3.36/1.01      | k1_setfam_1(k2_tarski(X0_40,k10_relat_1(X0_39,X0_41))) = k10_relat_1(k7_relat_1(X0_39,X0_40),X0_41) ),
% 3.36/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_375,plain,
% 3.36/1.01      ( k1_setfam_1(k2_tarski(X0_40,k10_relat_1(X0_39,X0_41))) = k10_relat_1(k7_relat_1(X0_39,X0_40),X0_41)
% 3.36/1.01      | v1_relat_1(X0_39) != iProver_top ),
% 3.36/1.01      inference(predicate_to_equality,[status(thm)],[c_161]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_691,plain,
% 3.36/1.01      ( k1_setfam_1(k2_tarski(X0_40,k10_relat_1(sK1,X0_41))) = k10_relat_1(k7_relat_1(sK1,X0_40),X0_41) ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_378,c_375]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1,plain,
% 3.36/1.01      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 3.36/1.01      inference(cnf_transformation,[],[f22]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_166,plain,
% 3.36/1.01      ( k2_tarski(X0_40,X1_40) = k2_tarski(X1_40,X0_40) ),
% 3.36/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_0,plain,
% 3.36/1.01      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
% 3.36/1.01      inference(cnf_transformation,[],[f32]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_167,plain,
% 3.36/1.01      ( r1_tarski(k1_setfam_1(k2_tarski(X0_40,X1_40)),X0_40) ),
% 3.36/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_370,plain,
% 3.36/1.01      ( r1_tarski(k1_setfam_1(k2_tarski(X0_40,X1_40)),X0_40) = iProver_top ),
% 3.36/1.01      inference(predicate_to_equality,[status(thm)],[c_167]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_503,plain,
% 3.36/1.01      ( r1_tarski(k1_setfam_1(k2_tarski(X0_40,X1_40)),X1_40) = iProver_top ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_166,c_370]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_849,plain,
% 3.36/1.01      ( r1_tarski(k10_relat_1(k7_relat_1(sK1,X0_40),X0_41),k10_relat_1(sK1,X0_41)) = iProver_top ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_691,c_503]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_1713,plain,
% 3.36/1.01      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0_40)),k10_relat_1(sK1,k9_relat_1(sK1,X0_40))) = iProver_top ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_1284,c_849]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_10848,plain,
% 3.36/1.01      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top ),
% 3.36/1.01      inference(superposition,[status(thm)],[c_949,c_1713]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_7,negated_conjecture,
% 3.36/1.01      ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
% 3.36/1.01      inference(cnf_transformation,[],[f31]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(c_12,plain,
% 3.36/1.01      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
% 3.36/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.36/1.01  
% 3.36/1.01  cnf(contradiction,plain,
% 3.36/1.01      ( $false ),
% 3.36/1.01      inference(minisat,[status(thm)],[c_10848,c_12]) ).
% 3.36/1.01  
% 3.36/1.01  
% 3.36/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.36/1.01  
% 3.36/1.01  ------                               Statistics
% 3.36/1.01  
% 3.36/1.01  ------ General
% 3.36/1.01  
% 3.36/1.01  abstr_ref_over_cycles:                  0
% 3.36/1.01  abstr_ref_under_cycles:                 0
% 3.36/1.01  gc_basic_clause_elim:                   0
% 3.36/1.01  forced_gc_time:                         0
% 3.36/1.01  parsing_time:                           0.022
% 3.36/1.01  unif_index_cands_time:                  0.
% 3.36/1.01  unif_index_add_time:                    0.
% 3.36/1.01  orderings_time:                         0.
% 3.36/1.01  out_proof_time:                         0.008
% 3.36/1.01  total_time:                             0.33
% 3.36/1.01  num_of_symbols:                         43
% 3.36/1.01  num_of_terms:                           10821
% 3.36/1.01  
% 3.36/1.01  ------ Preprocessing
% 3.36/1.01  
% 3.36/1.01  num_of_splits:                          0
% 3.36/1.01  num_of_split_atoms:                     0
% 3.36/1.01  num_of_reused_defs:                     0
% 3.36/1.01  num_eq_ax_congr_red:                    6
% 3.36/1.01  num_of_sem_filtered_clauses:            1
% 3.36/1.01  num_of_subtypes:                        4
% 3.36/1.01  monotx_restored_types:                  0
% 3.36/1.01  sat_num_of_epr_types:                   0
% 3.36/1.01  sat_num_of_non_cyclic_types:            0
% 3.36/1.01  sat_guarded_non_collapsed_types:        1
% 3.36/1.01  num_pure_diseq_elim:                    0
% 3.36/1.01  simp_replaced_by:                       0
% 3.36/1.01  res_preprocessed:                       61
% 3.36/1.01  prep_upred:                             0
% 3.36/1.01  prep_unflattend:                        4
% 3.36/1.01  smt_new_axioms:                         0
% 3.36/1.01  pred_elim_cands:                        2
% 3.36/1.01  pred_elim:                              0
% 3.36/1.01  pred_elim_cl:                           0
% 3.36/1.01  pred_elim_cycles:                       1
% 3.36/1.01  merged_defs:                            0
% 3.36/1.01  merged_defs_ncl:                        0
% 3.36/1.01  bin_hyper_res:                          0
% 3.36/1.01  prep_cycles:                            3
% 3.36/1.01  pred_elim_time:                         0.
% 3.36/1.01  splitting_time:                         0.
% 3.36/1.01  sem_filter_time:                        0.
% 3.36/1.01  monotx_time:                            0.
% 3.36/1.01  subtype_inf_time:                       0.
% 3.36/1.01  
% 3.36/1.01  ------ Problem properties
% 3.36/1.01  
% 3.36/1.01  clauses:                                10
% 3.36/1.01  conjectures:                            3
% 3.36/1.01  epr:                                    1
% 3.36/1.01  horn:                                   10
% 3.36/1.01  ground:                                 3
% 3.36/1.01  unary:                                  5
% 3.36/1.01  binary:                                 4
% 3.36/1.01  lits:                                   16
% 3.36/1.01  lits_eq:                                5
% 3.36/1.01  fd_pure:                                0
% 3.36/1.01  fd_pseudo:                              0
% 3.36/1.01  fd_cond:                                0
% 3.36/1.01  fd_pseudo_cond:                         0
% 3.36/1.01  ac_symbols:                             0
% 3.36/1.01  
% 3.36/1.01  ------ Propositional Solver
% 3.36/1.01  
% 3.36/1.01  prop_solver_calls:                      26
% 3.36/1.01  prop_fast_solver_calls:                 369
% 3.36/1.01  smt_solver_calls:                       0
% 3.36/1.01  smt_fast_solver_calls:                  0
% 3.36/1.01  prop_num_of_clauses:                    3083
% 3.36/1.01  prop_preprocess_simplified:             8884
% 3.36/1.01  prop_fo_subsumed:                       4
% 3.36/1.01  prop_solver_time:                       0.
% 3.36/1.01  smt_solver_time:                        0.
% 3.36/1.01  smt_fast_solver_time:                   0.
% 3.36/1.01  prop_fast_solver_time:                  0.
% 3.36/1.01  prop_unsat_core_time:                   0.
% 3.36/1.01  
% 3.36/1.01  ------ QBF
% 3.36/1.01  
% 3.36/1.01  qbf_q_res:                              0
% 3.36/1.01  qbf_num_tautologies:                    0
% 3.36/1.01  qbf_prep_cycles:                        0
% 3.36/1.01  
% 3.36/1.01  ------ BMC1
% 3.36/1.01  
% 3.36/1.01  bmc1_current_bound:                     -1
% 3.36/1.01  bmc1_last_solved_bound:                 -1
% 3.36/1.01  bmc1_unsat_core_size:                   -1
% 3.36/1.01  bmc1_unsat_core_parents_size:           -1
% 3.36/1.01  bmc1_merge_next_fun:                    0
% 3.36/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.36/1.01  
% 3.36/1.01  ------ Instantiation
% 3.36/1.01  
% 3.36/1.01  inst_num_of_clauses:                    1139
% 3.36/1.01  inst_num_in_passive:                    501
% 3.36/1.01  inst_num_in_active:                     460
% 3.36/1.01  inst_num_in_unprocessed:                178
% 3.36/1.01  inst_num_of_loops:                      470
% 3.36/1.01  inst_num_of_learning_restarts:          0
% 3.36/1.01  inst_num_moves_active_passive:          6
% 3.36/1.01  inst_lit_activity:                      0
% 3.36/1.01  inst_lit_activity_moves:                0
% 3.36/1.01  inst_num_tautologies:                   0
% 3.36/1.01  inst_num_prop_implied:                  0
% 3.36/1.01  inst_num_existing_simplified:           0
% 3.36/1.01  inst_num_eq_res_simplified:             0
% 3.36/1.01  inst_num_child_elim:                    0
% 3.36/1.01  inst_num_of_dismatching_blockings:      756
% 3.36/1.01  inst_num_of_non_proper_insts:           1670
% 3.36/1.01  inst_num_of_duplicates:                 0
% 3.36/1.01  inst_inst_num_from_inst_to_res:         0
% 3.36/1.01  inst_dismatching_checking_time:         0.
% 3.36/1.01  
% 3.36/1.01  ------ Resolution
% 3.36/1.01  
% 3.36/1.01  res_num_of_clauses:                     0
% 3.36/1.01  res_num_in_passive:                     0
% 3.36/1.01  res_num_in_active:                      0
% 3.36/1.01  res_num_of_loops:                       64
% 3.36/1.01  res_forward_subset_subsumed:            187
% 3.36/1.01  res_backward_subset_subsumed:           2
% 3.36/1.01  res_forward_subsumed:                   0
% 3.36/1.01  res_backward_subsumed:                  0
% 3.36/1.01  res_forward_subsumption_resolution:     0
% 3.36/1.01  res_backward_subsumption_resolution:    0
% 3.36/1.01  res_clause_to_clause_subsumption:       1175
% 3.36/1.01  res_orphan_elimination:                 0
% 3.36/1.01  res_tautology_del:                      164
% 3.36/1.01  res_num_eq_res_simplified:              0
% 3.36/1.01  res_num_sel_changes:                    0
% 3.36/1.01  res_moves_from_active_to_pass:          0
% 3.36/1.01  
% 3.36/1.01  ------ Superposition
% 3.36/1.01  
% 3.36/1.01  sup_time_total:                         0.
% 3.36/1.01  sup_time_generating:                    0.
% 3.36/1.01  sup_time_sim_full:                      0.
% 3.36/1.01  sup_time_sim_immed:                     0.
% 3.36/1.01  
% 3.36/1.01  sup_num_of_clauses:                     282
% 3.36/1.01  sup_num_in_active:                      92
% 3.36/1.01  sup_num_in_passive:                     190
% 3.36/1.01  sup_num_of_loops:                       93
% 3.36/1.01  sup_fw_superposition:                   638
% 3.36/1.01  sup_bw_superposition:                   478
% 3.36/1.01  sup_immediate_simplified:               404
% 3.36/1.01  sup_given_eliminated:                   0
% 3.36/1.01  comparisons_done:                       0
% 3.36/1.01  comparisons_avoided:                    0
% 3.36/1.01  
% 3.36/1.01  ------ Simplifications
% 3.36/1.01  
% 3.36/1.01  
% 3.36/1.01  sim_fw_subset_subsumed:                 2
% 3.36/1.01  sim_bw_subset_subsumed:                 3
% 3.36/1.01  sim_fw_subsumed:                        158
% 3.36/1.01  sim_bw_subsumed:                        1
% 3.36/1.01  sim_fw_subsumption_res:                 0
% 3.36/1.01  sim_bw_subsumption_res:                 0
% 3.36/1.01  sim_tautology_del:                      0
% 3.36/1.01  sim_eq_tautology_del:                   66
% 3.36/1.01  sim_eq_res_simp:                        0
% 3.36/1.01  sim_fw_demodulated:                     214
% 3.36/1.01  sim_bw_demodulated:                     5
% 3.36/1.01  sim_light_normalised:                   128
% 3.36/1.01  sim_joinable_taut:                      0
% 3.36/1.01  sim_joinable_simp:                      0
% 3.36/1.01  sim_ac_normalised:                      0
% 3.36/1.01  sim_smt_subsumption:                    0
% 3.36/1.01  
%------------------------------------------------------------------------------
