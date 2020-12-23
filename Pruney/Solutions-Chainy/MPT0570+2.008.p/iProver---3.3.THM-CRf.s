%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:36 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 107 expanded)
%              Number of clauses        :   31 (  32 expanded)
%              Number of leaves         :   14 (  25 expanded)
%              Depth                    :   12
%              Number of atoms          :  166 ( 262 expanded)
%              Number of equality atoms :   74 ( 128 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
            & r1_tarski(X0,k2_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      & r1_tarski(X0,k2_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      & r1_tarski(X0,k2_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k10_relat_1(X1,X0)
        & r1_tarski(X0,k2_relat_1(X1))
        & k1_xboole_0 != X0
        & v1_relat_1(X1) )
   => ( k1_xboole_0 = k10_relat_1(sK3,sK2)
      & r1_tarski(sK2,k2_relat_1(sK3))
      & k1_xboole_0 != sK2
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( k1_xboole_0 = k10_relat_1(sK3,sK2)
    & r1_tarski(sK2,k2_relat_1(sK3))
    & k1_xboole_0 != sK2
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f28])).

fof(f45,plain,(
    r1_tarski(sK2,k2_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f40,f38])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f32,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f25])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f35,f38])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f30,f38,f38])).

fof(f46,plain,(
    k1_xboole_0 = k10_relat_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k10_relat_1(X1,X0)
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_relat_1(X1),X0)
      | k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f44,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK2,k2_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_351,plain,
    ( r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_355,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1133,plain,
    ( k4_xboole_0(sK2,k2_relat_1(sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_351,c_355])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2486,plain,
    ( k1_setfam_1(k2_tarski(sK2,k2_relat_1(sK3))) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1133,c_9])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2488,plain,
    ( k1_setfam_1(k2_tarski(sK2,k2_relat_1(sK3))) = sK2 ),
    inference(demodulation,[status(thm)],[c_2486,c_7])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_360,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_357,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_379,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_0,c_9])).

cnf(c_401,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k1_setfam_1(k2_tarski(X1,X0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_357,c_379])).

cnf(c_7702,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | v1_xboole_0(k1_setfam_1(k2_tarski(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_360,c_401])).

cnf(c_8073,plain,
    ( r1_xboole_0(k2_relat_1(sK3),sK2) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2488,c_7702])).

cnf(c_12,negated_conjecture,
    ( k1_xboole_0 = k10_relat_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_11,plain,
    ( r1_xboole_0(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_352,plain,
    ( k10_relat_1(X0,X1) != k1_xboole_0
    | r1_xboole_0(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_823,plain,
    ( r1_xboole_0(k2_relat_1(sK3),sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_352])).

cnf(c_8,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_459,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_460,plain,
    ( k1_xboole_0 = sK2
    | v1_xboole_0(sK2) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_459])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_36,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_16,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8073,c_823,c_460,c_36,c_14,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.24/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/0.99  
% 3.24/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.24/0.99  
% 3.24/0.99  ------  iProver source info
% 3.24/0.99  
% 3.24/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.24/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.24/0.99  git: non_committed_changes: false
% 3.24/0.99  git: last_make_outside_of_git: false
% 3.24/0.99  
% 3.24/0.99  ------ 
% 3.24/0.99  
% 3.24/0.99  ------ Input Options
% 3.24/0.99  
% 3.24/0.99  --out_options                           all
% 3.24/0.99  --tptp_safe_out                         true
% 3.24/0.99  --problem_path                          ""
% 3.24/0.99  --include_path                          ""
% 3.24/0.99  --clausifier                            res/vclausify_rel
% 3.24/0.99  --clausifier_options                    --mode clausify
% 3.24/0.99  --stdin                                 false
% 3.24/0.99  --stats_out                             sel
% 3.24/0.99  
% 3.24/0.99  ------ General Options
% 3.24/0.99  
% 3.24/0.99  --fof                                   false
% 3.24/0.99  --time_out_real                         604.99
% 3.24/0.99  --time_out_virtual                      -1.
% 3.24/0.99  --symbol_type_check                     false
% 3.24/0.99  --clausify_out                          false
% 3.24/0.99  --sig_cnt_out                           false
% 3.24/0.99  --trig_cnt_out                          false
% 3.24/0.99  --trig_cnt_out_tolerance                1.
% 3.24/0.99  --trig_cnt_out_sk_spl                   false
% 3.24/0.99  --abstr_cl_out                          false
% 3.24/0.99  
% 3.24/0.99  ------ Global Options
% 3.24/0.99  
% 3.24/0.99  --schedule                              none
% 3.24/0.99  --add_important_lit                     false
% 3.24/0.99  --prop_solver_per_cl                    1000
% 3.24/0.99  --min_unsat_core                        false
% 3.24/0.99  --soft_assumptions                      false
% 3.24/0.99  --soft_lemma_size                       3
% 3.24/0.99  --prop_impl_unit_size                   0
% 3.24/0.99  --prop_impl_unit                        []
% 3.24/0.99  --share_sel_clauses                     true
% 3.24/0.99  --reset_solvers                         false
% 3.24/0.99  --bc_imp_inh                            [conj_cone]
% 3.24/0.99  --conj_cone_tolerance                   3.
% 3.24/0.99  --extra_neg_conj                        none
% 3.24/0.99  --large_theory_mode                     true
% 3.24/0.99  --prolific_symb_bound                   200
% 3.24/0.99  --lt_threshold                          2000
% 3.24/0.99  --clause_weak_htbl                      true
% 3.24/0.99  --gc_record_bc_elim                     false
% 3.24/0.99  
% 3.24/0.99  ------ Preprocessing Options
% 3.24/0.99  
% 3.24/0.99  --preprocessing_flag                    true
% 3.24/0.99  --time_out_prep_mult                    0.1
% 3.24/0.99  --splitting_mode                        input
% 3.24/0.99  --splitting_grd                         true
% 3.24/0.99  --splitting_cvd                         false
% 3.24/0.99  --splitting_cvd_svl                     false
% 3.24/0.99  --splitting_nvd                         32
% 3.24/0.99  --sub_typing                            true
% 3.24/0.99  --prep_gs_sim                           false
% 3.24/0.99  --prep_unflatten                        true
% 3.24/0.99  --prep_res_sim                          true
% 3.24/0.99  --prep_upred                            true
% 3.24/0.99  --prep_sem_filter                       exhaustive
% 3.24/0.99  --prep_sem_filter_out                   false
% 3.24/0.99  --pred_elim                             false
% 3.24/0.99  --res_sim_input                         true
% 3.24/0.99  --eq_ax_congr_red                       true
% 3.24/0.99  --pure_diseq_elim                       true
% 3.24/0.99  --brand_transform                       false
% 3.24/0.99  --non_eq_to_eq                          false
% 3.24/0.99  --prep_def_merge                        true
% 3.24/0.99  --prep_def_merge_prop_impl              false
% 3.24/0.99  --prep_def_merge_mbd                    true
% 3.24/0.99  --prep_def_merge_tr_red                 false
% 3.24/0.99  --prep_def_merge_tr_cl                  false
% 3.24/0.99  --smt_preprocessing                     true
% 3.24/0.99  --smt_ac_axioms                         fast
% 3.24/0.99  --preprocessed_out                      false
% 3.24/0.99  --preprocessed_stats                    false
% 3.24/0.99  
% 3.24/0.99  ------ Abstraction refinement Options
% 3.24/0.99  
% 3.24/0.99  --abstr_ref                             []
% 3.24/0.99  --abstr_ref_prep                        false
% 3.24/0.99  --abstr_ref_until_sat                   false
% 3.24/0.99  --abstr_ref_sig_restrict                funpre
% 3.24/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.24/0.99  --abstr_ref_under                       []
% 3.24/0.99  
% 3.24/0.99  ------ SAT Options
% 3.24/0.99  
% 3.24/0.99  --sat_mode                              false
% 3.24/0.99  --sat_fm_restart_options                ""
% 3.24/0.99  --sat_gr_def                            false
% 3.24/0.99  --sat_epr_types                         true
% 3.24/0.99  --sat_non_cyclic_types                  false
% 3.24/0.99  --sat_finite_models                     false
% 3.24/0.99  --sat_fm_lemmas                         false
% 3.24/0.99  --sat_fm_prep                           false
% 3.24/0.99  --sat_fm_uc_incr                        true
% 3.24/0.99  --sat_out_model                         small
% 3.24/0.99  --sat_out_clauses                       false
% 3.24/0.99  
% 3.24/0.99  ------ QBF Options
% 3.24/0.99  
% 3.24/0.99  --qbf_mode                              false
% 3.24/0.99  --qbf_elim_univ                         false
% 3.24/0.99  --qbf_dom_inst                          none
% 3.24/0.99  --qbf_dom_pre_inst                      false
% 3.24/0.99  --qbf_sk_in                             false
% 3.24/0.99  --qbf_pred_elim                         true
% 3.24/0.99  --qbf_split                             512
% 3.24/0.99  
% 3.24/0.99  ------ BMC1 Options
% 3.24/0.99  
% 3.24/0.99  --bmc1_incremental                      false
% 3.24/0.99  --bmc1_axioms                           reachable_all
% 3.24/0.99  --bmc1_min_bound                        0
% 3.24/0.99  --bmc1_max_bound                        -1
% 3.24/0.99  --bmc1_max_bound_default                -1
% 3.24/0.99  --bmc1_symbol_reachability              true
% 3.24/0.99  --bmc1_property_lemmas                  false
% 3.24/0.99  --bmc1_k_induction                      false
% 3.24/0.99  --bmc1_non_equiv_states                 false
% 3.24/0.99  --bmc1_deadlock                         false
% 3.24/0.99  --bmc1_ucm                              false
% 3.24/0.99  --bmc1_add_unsat_core                   none
% 3.24/0.99  --bmc1_unsat_core_children              false
% 3.24/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.24/0.99  --bmc1_out_stat                         full
% 3.24/0.99  --bmc1_ground_init                      false
% 3.24/0.99  --bmc1_pre_inst_next_state              false
% 3.24/0.99  --bmc1_pre_inst_state                   false
% 3.24/0.99  --bmc1_pre_inst_reach_state             false
% 3.24/0.99  --bmc1_out_unsat_core                   false
% 3.24/0.99  --bmc1_aig_witness_out                  false
% 3.24/0.99  --bmc1_verbose                          false
% 3.24/0.99  --bmc1_dump_clauses_tptp                false
% 3.24/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.24/0.99  --bmc1_dump_file                        -
% 3.24/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.24/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.24/0.99  --bmc1_ucm_extend_mode                  1
% 3.24/0.99  --bmc1_ucm_init_mode                    2
% 3.24/0.99  --bmc1_ucm_cone_mode                    none
% 3.24/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.24/0.99  --bmc1_ucm_relax_model                  4
% 3.24/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.24/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.24/0.99  --bmc1_ucm_layered_model                none
% 3.24/0.99  --bmc1_ucm_max_lemma_size               10
% 3.24/0.99  
% 3.24/0.99  ------ AIG Options
% 3.24/0.99  
% 3.24/0.99  --aig_mode                              false
% 3.24/0.99  
% 3.24/0.99  ------ Instantiation Options
% 3.24/0.99  
% 3.24/0.99  --instantiation_flag                    true
% 3.24/0.99  --inst_sos_flag                         false
% 3.24/0.99  --inst_sos_phase                        true
% 3.24/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.24/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.24/0.99  --inst_lit_sel_side                     num_symb
% 3.24/0.99  --inst_solver_per_active                1400
% 3.24/0.99  --inst_solver_calls_frac                1.
% 3.24/0.99  --inst_passive_queue_type               priority_queues
% 3.24/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.24/0.99  --inst_passive_queues_freq              [25;2]
% 3.24/0.99  --inst_dismatching                      true
% 3.24/0.99  --inst_eager_unprocessed_to_passive     true
% 3.24/0.99  --inst_prop_sim_given                   true
% 3.24/0.99  --inst_prop_sim_new                     false
% 3.24/0.99  --inst_subs_new                         false
% 3.24/0.99  --inst_eq_res_simp                      false
% 3.24/0.99  --inst_subs_given                       false
% 3.24/0.99  --inst_orphan_elimination               true
% 3.24/0.99  --inst_learning_loop_flag               true
% 3.24/0.99  --inst_learning_start                   3000
% 3.24/0.99  --inst_learning_factor                  2
% 3.24/0.99  --inst_start_prop_sim_after_learn       3
% 3.24/0.99  --inst_sel_renew                        solver
% 3.24/0.99  --inst_lit_activity_flag                true
% 3.24/0.99  --inst_restr_to_given                   false
% 3.24/0.99  --inst_activity_threshold               500
% 3.24/0.99  --inst_out_proof                        true
% 3.24/0.99  
% 3.24/0.99  ------ Resolution Options
% 3.24/0.99  
% 3.24/0.99  --resolution_flag                       true
% 3.24/0.99  --res_lit_sel                           adaptive
% 3.24/0.99  --res_lit_sel_side                      none
% 3.24/0.99  --res_ordering                          kbo
% 3.24/0.99  --res_to_prop_solver                    active
% 3.24/0.99  --res_prop_simpl_new                    false
% 3.24/0.99  --res_prop_simpl_given                  true
% 3.24/0.99  --res_passive_queue_type                priority_queues
% 3.24/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.24/0.99  --res_passive_queues_freq               [15;5]
% 3.24/0.99  --res_forward_subs                      full
% 3.24/0.99  --res_backward_subs                     full
% 3.24/0.99  --res_forward_subs_resolution           true
% 3.24/0.99  --res_backward_subs_resolution          true
% 3.24/0.99  --res_orphan_elimination                true
% 3.24/0.99  --res_time_limit                        2.
% 3.24/0.99  --res_out_proof                         true
% 3.24/0.99  
% 3.24/0.99  ------ Superposition Options
% 3.24/0.99  
% 3.24/0.99  --superposition_flag                    true
% 3.24/0.99  --sup_passive_queue_type                priority_queues
% 3.24/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.24/0.99  --sup_passive_queues_freq               [1;4]
% 3.24/0.99  --demod_completeness_check              fast
% 3.24/0.99  --demod_use_ground                      true
% 3.24/0.99  --sup_to_prop_solver                    passive
% 3.24/0.99  --sup_prop_simpl_new                    true
% 3.24/0.99  --sup_prop_simpl_given                  true
% 3.24/0.99  --sup_fun_splitting                     false
% 3.24/0.99  --sup_smt_interval                      50000
% 3.24/0.99  
% 3.24/0.99  ------ Superposition Simplification Setup
% 3.24/0.99  
% 3.24/0.99  --sup_indices_passive                   []
% 3.24/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.24/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/0.99  --sup_full_bw                           [BwDemod]
% 3.24/0.99  --sup_immed_triv                        [TrivRules]
% 3.24/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.24/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/0.99  --sup_immed_bw_main                     []
% 3.24/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.24/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/0.99  
% 3.24/0.99  ------ Combination Options
% 3.24/0.99  
% 3.24/0.99  --comb_res_mult                         3
% 3.24/0.99  --comb_sup_mult                         2
% 3.24/0.99  --comb_inst_mult                        10
% 3.24/0.99  
% 3.24/0.99  ------ Debug Options
% 3.24/0.99  
% 3.24/0.99  --dbg_backtrace                         false
% 3.24/0.99  --dbg_dump_prop_clauses                 false
% 3.24/0.99  --dbg_dump_prop_clauses_file            -
% 3.24/0.99  --dbg_out_stat                          false
% 3.24/0.99  ------ Parsing...
% 3.24/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.24/0.99  
% 3.24/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.24/0.99  
% 3.24/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.24/0.99  
% 3.24/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.24/0.99  ------ Proving...
% 3.24/0.99  ------ Problem Properties 
% 3.24/0.99  
% 3.24/0.99  
% 3.24/0.99  clauses                                 16
% 3.24/0.99  conjectures                             4
% 3.24/0.99  EPR                                     5
% 3.24/0.99  Horn                                    14
% 3.24/0.99  unary                                   8
% 3.24/0.99  binary                                  5
% 3.24/0.99  lits                                    27
% 3.24/0.99  lits eq                                 9
% 3.24/0.99  fd_pure                                 0
% 3.24/0.99  fd_pseudo                               0
% 3.24/0.99  fd_cond                                 0
% 3.24/0.99  fd_pseudo_cond                          1
% 3.24/0.99  AC symbols                              0
% 3.24/0.99  
% 3.24/0.99  ------ Input Options Time Limit: Unbounded
% 3.24/0.99  
% 3.24/0.99  
% 3.24/0.99  ------ 
% 3.24/0.99  Current options:
% 3.24/0.99  ------ 
% 3.24/0.99  
% 3.24/0.99  ------ Input Options
% 3.24/0.99  
% 3.24/0.99  --out_options                           all
% 3.24/0.99  --tptp_safe_out                         true
% 3.24/0.99  --problem_path                          ""
% 3.24/0.99  --include_path                          ""
% 3.24/0.99  --clausifier                            res/vclausify_rel
% 3.24/0.99  --clausifier_options                    --mode clausify
% 3.24/0.99  --stdin                                 false
% 3.24/0.99  --stats_out                             sel
% 3.24/0.99  
% 3.24/0.99  ------ General Options
% 3.24/0.99  
% 3.24/0.99  --fof                                   false
% 3.24/0.99  --time_out_real                         604.99
% 3.24/0.99  --time_out_virtual                      -1.
% 3.24/0.99  --symbol_type_check                     false
% 3.24/0.99  --clausify_out                          false
% 3.24/0.99  --sig_cnt_out                           false
% 3.24/0.99  --trig_cnt_out                          false
% 3.24/0.99  --trig_cnt_out_tolerance                1.
% 3.24/0.99  --trig_cnt_out_sk_spl                   false
% 3.24/0.99  --abstr_cl_out                          false
% 3.24/0.99  
% 3.24/0.99  ------ Global Options
% 3.24/0.99  
% 3.24/0.99  --schedule                              none
% 3.24/0.99  --add_important_lit                     false
% 3.24/0.99  --prop_solver_per_cl                    1000
% 3.24/0.99  --min_unsat_core                        false
% 3.24/0.99  --soft_assumptions                      false
% 3.24/0.99  --soft_lemma_size                       3
% 3.24/0.99  --prop_impl_unit_size                   0
% 3.24/0.99  --prop_impl_unit                        []
% 3.24/0.99  --share_sel_clauses                     true
% 3.24/0.99  --reset_solvers                         false
% 3.24/0.99  --bc_imp_inh                            [conj_cone]
% 3.24/0.99  --conj_cone_tolerance                   3.
% 3.24/0.99  --extra_neg_conj                        none
% 3.24/0.99  --large_theory_mode                     true
% 3.24/0.99  --prolific_symb_bound                   200
% 3.24/0.99  --lt_threshold                          2000
% 3.24/0.99  --clause_weak_htbl                      true
% 3.24/0.99  --gc_record_bc_elim                     false
% 3.24/0.99  
% 3.24/0.99  ------ Preprocessing Options
% 3.24/0.99  
% 3.24/0.99  --preprocessing_flag                    true
% 3.24/0.99  --time_out_prep_mult                    0.1
% 3.24/0.99  --splitting_mode                        input
% 3.24/0.99  --splitting_grd                         true
% 3.24/0.99  --splitting_cvd                         false
% 3.24/0.99  --splitting_cvd_svl                     false
% 3.24/0.99  --splitting_nvd                         32
% 3.24/0.99  --sub_typing                            true
% 3.24/0.99  --prep_gs_sim                           false
% 3.24/0.99  --prep_unflatten                        true
% 3.24/0.99  --prep_res_sim                          true
% 3.24/0.99  --prep_upred                            true
% 3.24/0.99  --prep_sem_filter                       exhaustive
% 3.24/0.99  --prep_sem_filter_out                   false
% 3.24/0.99  --pred_elim                             false
% 3.24/0.99  --res_sim_input                         true
% 3.24/0.99  --eq_ax_congr_red                       true
% 3.24/0.99  --pure_diseq_elim                       true
% 3.24/0.99  --brand_transform                       false
% 3.24/0.99  --non_eq_to_eq                          false
% 3.24/0.99  --prep_def_merge                        true
% 3.24/0.99  --prep_def_merge_prop_impl              false
% 3.24/0.99  --prep_def_merge_mbd                    true
% 3.24/0.99  --prep_def_merge_tr_red                 false
% 3.24/0.99  --prep_def_merge_tr_cl                  false
% 3.24/0.99  --smt_preprocessing                     true
% 3.24/0.99  --smt_ac_axioms                         fast
% 3.24/0.99  --preprocessed_out                      false
% 3.24/0.99  --preprocessed_stats                    false
% 3.24/0.99  
% 3.24/0.99  ------ Abstraction refinement Options
% 3.24/0.99  
% 3.24/0.99  --abstr_ref                             []
% 3.24/0.99  --abstr_ref_prep                        false
% 3.24/0.99  --abstr_ref_until_sat                   false
% 3.24/0.99  --abstr_ref_sig_restrict                funpre
% 3.24/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.24/0.99  --abstr_ref_under                       []
% 3.24/0.99  
% 3.24/0.99  ------ SAT Options
% 3.24/0.99  
% 3.24/0.99  --sat_mode                              false
% 3.24/0.99  --sat_fm_restart_options                ""
% 3.24/0.99  --sat_gr_def                            false
% 3.24/0.99  --sat_epr_types                         true
% 3.24/0.99  --sat_non_cyclic_types                  false
% 3.24/0.99  --sat_finite_models                     false
% 3.24/0.99  --sat_fm_lemmas                         false
% 3.24/0.99  --sat_fm_prep                           false
% 3.24/0.99  --sat_fm_uc_incr                        true
% 3.24/0.99  --sat_out_model                         small
% 3.24/0.99  --sat_out_clauses                       false
% 3.24/0.99  
% 3.24/0.99  ------ QBF Options
% 3.24/0.99  
% 3.24/0.99  --qbf_mode                              false
% 3.24/0.99  --qbf_elim_univ                         false
% 3.24/0.99  --qbf_dom_inst                          none
% 3.24/0.99  --qbf_dom_pre_inst                      false
% 3.24/0.99  --qbf_sk_in                             false
% 3.24/0.99  --qbf_pred_elim                         true
% 3.24/0.99  --qbf_split                             512
% 3.24/0.99  
% 3.24/0.99  ------ BMC1 Options
% 3.24/0.99  
% 3.24/0.99  --bmc1_incremental                      false
% 3.24/0.99  --bmc1_axioms                           reachable_all
% 3.24/0.99  --bmc1_min_bound                        0
% 3.24/0.99  --bmc1_max_bound                        -1
% 3.24/0.99  --bmc1_max_bound_default                -1
% 3.24/0.99  --bmc1_symbol_reachability              true
% 3.24/0.99  --bmc1_property_lemmas                  false
% 3.24/0.99  --bmc1_k_induction                      false
% 3.24/0.99  --bmc1_non_equiv_states                 false
% 3.24/0.99  --bmc1_deadlock                         false
% 3.24/0.99  --bmc1_ucm                              false
% 3.24/0.99  --bmc1_add_unsat_core                   none
% 3.24/0.99  --bmc1_unsat_core_children              false
% 3.24/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.24/0.99  --bmc1_out_stat                         full
% 3.24/0.99  --bmc1_ground_init                      false
% 3.24/0.99  --bmc1_pre_inst_next_state              false
% 3.24/0.99  --bmc1_pre_inst_state                   false
% 3.24/0.99  --bmc1_pre_inst_reach_state             false
% 3.24/0.99  --bmc1_out_unsat_core                   false
% 3.24/0.99  --bmc1_aig_witness_out                  false
% 3.24/0.99  --bmc1_verbose                          false
% 3.24/0.99  --bmc1_dump_clauses_tptp                false
% 3.24/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.24/0.99  --bmc1_dump_file                        -
% 3.24/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.24/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.24/0.99  --bmc1_ucm_extend_mode                  1
% 3.24/0.99  --bmc1_ucm_init_mode                    2
% 3.24/0.99  --bmc1_ucm_cone_mode                    none
% 3.24/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.24/0.99  --bmc1_ucm_relax_model                  4
% 3.24/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.24/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.24/0.99  --bmc1_ucm_layered_model                none
% 3.24/0.99  --bmc1_ucm_max_lemma_size               10
% 3.24/0.99  
% 3.24/0.99  ------ AIG Options
% 3.24/0.99  
% 3.24/0.99  --aig_mode                              false
% 3.24/0.99  
% 3.24/0.99  ------ Instantiation Options
% 3.24/0.99  
% 3.24/0.99  --instantiation_flag                    true
% 3.24/0.99  --inst_sos_flag                         false
% 3.24/0.99  --inst_sos_phase                        true
% 3.24/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.24/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.24/0.99  --inst_lit_sel_side                     num_symb
% 3.24/0.99  --inst_solver_per_active                1400
% 3.24/0.99  --inst_solver_calls_frac                1.
% 3.24/0.99  --inst_passive_queue_type               priority_queues
% 3.24/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.24/0.99  --inst_passive_queues_freq              [25;2]
% 3.24/0.99  --inst_dismatching                      true
% 3.24/0.99  --inst_eager_unprocessed_to_passive     true
% 3.24/0.99  --inst_prop_sim_given                   true
% 3.24/0.99  --inst_prop_sim_new                     false
% 3.24/0.99  --inst_subs_new                         false
% 3.24/0.99  --inst_eq_res_simp                      false
% 3.24/0.99  --inst_subs_given                       false
% 3.24/0.99  --inst_orphan_elimination               true
% 3.24/0.99  --inst_learning_loop_flag               true
% 3.24/0.99  --inst_learning_start                   3000
% 3.24/0.99  --inst_learning_factor                  2
% 3.24/0.99  --inst_start_prop_sim_after_learn       3
% 3.24/0.99  --inst_sel_renew                        solver
% 3.24/0.99  --inst_lit_activity_flag                true
% 3.24/0.99  --inst_restr_to_given                   false
% 3.24/0.99  --inst_activity_threshold               500
% 3.24/0.99  --inst_out_proof                        true
% 3.24/0.99  
% 3.24/0.99  ------ Resolution Options
% 3.24/0.99  
% 3.24/0.99  --resolution_flag                       true
% 3.24/0.99  --res_lit_sel                           adaptive
% 3.24/0.99  --res_lit_sel_side                      none
% 3.24/0.99  --res_ordering                          kbo
% 3.24/0.99  --res_to_prop_solver                    active
% 3.24/0.99  --res_prop_simpl_new                    false
% 3.24/0.99  --res_prop_simpl_given                  true
% 3.24/0.99  --res_passive_queue_type                priority_queues
% 3.24/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.24/0.99  --res_passive_queues_freq               [15;5]
% 3.24/0.99  --res_forward_subs                      full
% 3.24/0.99  --res_backward_subs                     full
% 3.24/0.99  --res_forward_subs_resolution           true
% 3.24/0.99  --res_backward_subs_resolution          true
% 3.24/0.99  --res_orphan_elimination                true
% 3.24/0.99  --res_time_limit                        2.
% 3.24/0.99  --res_out_proof                         true
% 3.24/0.99  
% 3.24/0.99  ------ Superposition Options
% 3.24/0.99  
% 3.24/0.99  --superposition_flag                    true
% 3.24/0.99  --sup_passive_queue_type                priority_queues
% 3.24/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.24/0.99  --sup_passive_queues_freq               [1;4]
% 3.24/0.99  --demod_completeness_check              fast
% 3.24/0.99  --demod_use_ground                      true
% 3.24/0.99  --sup_to_prop_solver                    passive
% 3.24/0.99  --sup_prop_simpl_new                    true
% 3.24/0.99  --sup_prop_simpl_given                  true
% 3.24/0.99  --sup_fun_splitting                     false
% 3.24/0.99  --sup_smt_interval                      50000
% 3.24/0.99  
% 3.24/0.99  ------ Superposition Simplification Setup
% 3.24/0.99  
% 3.24/0.99  --sup_indices_passive                   []
% 3.24/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.24/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/0.99  --sup_full_bw                           [BwDemod]
% 3.24/0.99  --sup_immed_triv                        [TrivRules]
% 3.24/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.24/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/0.99  --sup_immed_bw_main                     []
% 3.24/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.24/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/0.99  
% 3.24/0.99  ------ Combination Options
% 3.24/0.99  
% 3.24/0.99  --comb_res_mult                         3
% 3.24/0.99  --comb_sup_mult                         2
% 3.24/0.99  --comb_inst_mult                        10
% 3.24/0.99  
% 3.24/0.99  ------ Debug Options
% 3.24/0.99  
% 3.24/0.99  --dbg_backtrace                         false
% 3.24/0.99  --dbg_dump_prop_clauses                 false
% 3.24/0.99  --dbg_dump_prop_clauses_file            -
% 3.24/0.99  --dbg_out_stat                          false
% 3.24/0.99  
% 3.24/0.99  
% 3.24/0.99  
% 3.24/0.99  
% 3.24/0.99  ------ Proving...
% 3.24/0.99  
% 3.24/0.99  
% 3.24/0.99  % SZS status Theorem for theBenchmark.p
% 3.24/0.99  
% 3.24/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.24/0.99  
% 3.24/0.99  fof(f11,conjecture,(
% 3.24/0.99    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 3.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/0.99  
% 3.24/0.99  fof(f12,negated_conjecture,(
% 3.24/0.99    ~! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 3.24/0.99    inference(negated_conjecture,[],[f11])).
% 3.24/0.99  
% 3.24/0.99  fof(f19,plain,(
% 3.24/0.99    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 3.24/0.99    inference(ennf_transformation,[],[f12])).
% 3.24/0.99  
% 3.24/0.99  fof(f20,plain,(
% 3.24/0.99    ? [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 3.24/0.99    inference(flattening,[],[f19])).
% 3.24/0.99  
% 3.24/0.99  fof(f28,plain,(
% 3.24/0.99    ? [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1)) => (k1_xboole_0 = k10_relat_1(sK3,sK2) & r1_tarski(sK2,k2_relat_1(sK3)) & k1_xboole_0 != sK2 & v1_relat_1(sK3))),
% 3.24/0.99    introduced(choice_axiom,[])).
% 3.24/0.99  
% 3.24/0.99  fof(f29,plain,(
% 3.24/0.99    k1_xboole_0 = k10_relat_1(sK3,sK2) & r1_tarski(sK2,k2_relat_1(sK3)) & k1_xboole_0 != sK2 & v1_relat_1(sK3)),
% 3.24/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f28])).
% 3.24/0.99  
% 3.24/0.99  fof(f45,plain,(
% 3.24/0.99    r1_tarski(sK2,k2_relat_1(sK3))),
% 3.24/0.99    inference(cnf_transformation,[],[f29])).
% 3.24/0.99  
% 3.24/0.99  fof(f5,axiom,(
% 3.24/0.99    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 3.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/0.99  
% 3.24/0.99  fof(f14,plain,(
% 3.24/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 3.24/0.99    inference(unused_predicate_definition_removal,[],[f5])).
% 3.24/0.99  
% 3.24/0.99  fof(f16,plain,(
% 3.24/0.99    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 3.24/0.99    inference(ennf_transformation,[],[f14])).
% 3.24/0.99  
% 3.24/0.99  fof(f36,plain,(
% 3.24/0.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 3.24/0.99    inference(cnf_transformation,[],[f16])).
% 3.24/0.99  
% 3.24/0.99  fof(f9,axiom,(
% 3.24/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/0.99  
% 3.24/0.99  fof(f40,plain,(
% 3.24/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.24/0.99    inference(cnf_transformation,[],[f9])).
% 3.24/0.99  
% 3.24/0.99  fof(f7,axiom,(
% 3.24/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/0.99  
% 3.24/0.99  fof(f38,plain,(
% 3.24/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.24/0.99    inference(cnf_transformation,[],[f7])).
% 3.24/0.99  
% 3.24/0.99  fof(f50,plain,(
% 3.24/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.24/0.99    inference(definition_unfolding,[],[f40,f38])).
% 3.24/0.99  
% 3.24/0.99  fof(f6,axiom,(
% 3.24/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/0.99  
% 3.24/0.99  fof(f37,plain,(
% 3.24/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.24/0.99    inference(cnf_transformation,[],[f6])).
% 3.24/0.99  
% 3.24/0.99  fof(f2,axiom,(
% 3.24/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/0.99  
% 3.24/0.99  fof(f21,plain,(
% 3.24/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.24/0.99    inference(nnf_transformation,[],[f2])).
% 3.24/0.99  
% 3.24/0.99  fof(f22,plain,(
% 3.24/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.24/0.99    inference(rectify,[],[f21])).
% 3.24/0.99  
% 3.24/0.99  fof(f23,plain,(
% 3.24/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.24/0.99    introduced(choice_axiom,[])).
% 3.24/0.99  
% 3.24/0.99  fof(f24,plain,(
% 3.24/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.24/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 3.24/0.99  
% 3.24/0.99  fof(f32,plain,(
% 3.24/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.24/0.99    inference(cnf_transformation,[],[f24])).
% 3.24/0.99  
% 3.24/0.99  fof(f4,axiom,(
% 3.24/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/0.99  
% 3.24/0.99  fof(f13,plain,(
% 3.24/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.24/0.99    inference(rectify,[],[f4])).
% 3.24/0.99  
% 3.24/0.99  fof(f15,plain,(
% 3.24/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.24/0.99    inference(ennf_transformation,[],[f13])).
% 3.24/0.99  
% 3.24/0.99  fof(f25,plain,(
% 3.24/0.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 3.24/0.99    introduced(choice_axiom,[])).
% 3.24/0.99  
% 3.24/0.99  fof(f26,plain,(
% 3.24/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.24/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f25])).
% 3.24/0.99  
% 3.24/0.99  fof(f35,plain,(
% 3.24/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.24/0.99    inference(cnf_transformation,[],[f26])).
% 3.24/0.99  
% 3.24/0.99  fof(f48,plain,(
% 3.24/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.24/0.99    inference(definition_unfolding,[],[f35,f38])).
% 3.24/0.99  
% 3.24/0.99  fof(f1,axiom,(
% 3.24/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/0.99  
% 3.24/0.99  fof(f30,plain,(
% 3.24/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.24/0.99    inference(cnf_transformation,[],[f1])).
% 3.24/0.99  
% 3.24/0.99  fof(f47,plain,(
% 3.24/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.24/0.99    inference(definition_unfolding,[],[f30,f38,f38])).
% 3.24/0.99  
% 3.24/0.99  fof(f46,plain,(
% 3.24/0.99    k1_xboole_0 = k10_relat_1(sK3,sK2)),
% 3.24/0.99    inference(cnf_transformation,[],[f29])).
% 3.24/0.99  
% 3.24/0.99  fof(f10,axiom,(
% 3.24/0.99    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 3.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/0.99  
% 3.24/0.99  fof(f18,plain,(
% 3.24/0.99    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.24/0.99    inference(ennf_transformation,[],[f10])).
% 3.24/0.99  
% 3.24/0.99  fof(f27,plain,(
% 3.24/0.99    ! [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.24/0.99    inference(nnf_transformation,[],[f18])).
% 3.24/0.99  
% 3.24/0.99  fof(f41,plain,(
% 3.24/0.99    ( ! [X0,X1] : (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.24/0.99    inference(cnf_transformation,[],[f27])).
% 3.24/0.99  
% 3.24/0.99  fof(f8,axiom,(
% 3.24/0.99    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/0.99  
% 3.24/0.99  fof(f17,plain,(
% 3.24/0.99    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.24/0.99    inference(ennf_transformation,[],[f8])).
% 3.24/0.99  
% 3.24/0.99  fof(f39,plain,(
% 3.24/0.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.24/0.99    inference(cnf_transformation,[],[f17])).
% 3.24/0.99  
% 3.24/0.99  fof(f3,axiom,(
% 3.24/0.99    v1_xboole_0(k1_xboole_0)),
% 3.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/0.99  
% 3.24/0.99  fof(f33,plain,(
% 3.24/0.99    v1_xboole_0(k1_xboole_0)),
% 3.24/0.99    inference(cnf_transformation,[],[f3])).
% 3.24/0.99  
% 3.24/0.99  fof(f44,plain,(
% 3.24/0.99    k1_xboole_0 != sK2),
% 3.24/0.99    inference(cnf_transformation,[],[f29])).
% 3.24/0.99  
% 3.24/0.99  fof(f43,plain,(
% 3.24/0.99    v1_relat_1(sK3)),
% 3.24/0.99    inference(cnf_transformation,[],[f29])).
% 3.24/0.99  
% 3.24/0.99  cnf(c_13,negated_conjecture,
% 3.24/0.99      ( r1_tarski(sK2,k2_relat_1(sK3)) ),
% 3.24/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_351,plain,
% 3.24/0.99      ( r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_6,plain,
% 3.24/0.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.24/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_355,plain,
% 3.24/0.99      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 3.24/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_1133,plain,
% 3.24/0.99      ( k4_xboole_0(sK2,k2_relat_1(sK3)) = k1_xboole_0 ),
% 3.24/0.99      inference(superposition,[status(thm)],[c_351,c_355]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_9,plain,
% 3.24/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 3.24/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_2486,plain,
% 3.24/0.99      ( k1_setfam_1(k2_tarski(sK2,k2_relat_1(sK3))) = k4_xboole_0(sK2,k1_xboole_0) ),
% 3.24/0.99      inference(superposition,[status(thm)],[c_1133,c_9]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_7,plain,
% 3.24/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.24/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_2488,plain,
% 3.24/0.99      ( k1_setfam_1(k2_tarski(sK2,k2_relat_1(sK3))) = sK2 ),
% 3.24/0.99      inference(demodulation,[status(thm)],[c_2486,c_7]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_1,plain,
% 3.24/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.24/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_360,plain,
% 3.24/0.99      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.24/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_4,plain,
% 3.24/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.24/0.99      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 3.24/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_357,plain,
% 3.24/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 3.24/0.99      | r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) != iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_0,plain,
% 3.24/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.24/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_379,plain,
% 3.24/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 3.24/0.99      inference(light_normalisation,[status(thm)],[c_0,c_9]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_401,plain,
% 3.24/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 3.24/0.99      | r2_hidden(X2,k1_setfam_1(k2_tarski(X1,X0))) != iProver_top ),
% 3.24/0.99      inference(light_normalisation,[status(thm)],[c_357,c_379]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_7702,plain,
% 3.24/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 3.24/0.99      | v1_xboole_0(k1_setfam_1(k2_tarski(X1,X0))) = iProver_top ),
% 3.24/0.99      inference(superposition,[status(thm)],[c_360,c_401]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_8073,plain,
% 3.24/0.99      ( r1_xboole_0(k2_relat_1(sK3),sK2) != iProver_top
% 3.24/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 3.24/0.99      inference(superposition,[status(thm)],[c_2488,c_7702]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_12,negated_conjecture,
% 3.24/0.99      ( k1_xboole_0 = k10_relat_1(sK3,sK2) ),
% 3.24/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_11,plain,
% 3.24/0.99      ( r1_xboole_0(k2_relat_1(X0),X1)
% 3.24/0.99      | ~ v1_relat_1(X0)
% 3.24/0.99      | k10_relat_1(X0,X1) != k1_xboole_0 ),
% 3.24/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_352,plain,
% 3.24/0.99      ( k10_relat_1(X0,X1) != k1_xboole_0
% 3.24/0.99      | r1_xboole_0(k2_relat_1(X0),X1) = iProver_top
% 3.24/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_823,plain,
% 3.24/0.99      ( r1_xboole_0(k2_relat_1(sK3),sK2) = iProver_top
% 3.24/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.24/0.99      inference(superposition,[status(thm)],[c_12,c_352]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_8,plain,
% 3.24/0.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 3.24/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_459,plain,
% 3.24/0.99      ( ~ v1_xboole_0(sK2)
% 3.24/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 3.24/0.99      | k1_xboole_0 = sK2 ),
% 3.24/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_460,plain,
% 3.24/0.99      ( k1_xboole_0 = sK2
% 3.24/0.99      | v1_xboole_0(sK2) != iProver_top
% 3.24/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_459]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_3,plain,
% 3.24/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.24/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_36,plain,
% 3.24/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_14,negated_conjecture,
% 3.24/0.99      ( k1_xboole_0 != sK2 ),
% 3.24/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_15,negated_conjecture,
% 3.24/0.99      ( v1_relat_1(sK3) ),
% 3.24/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_16,plain,
% 3.24/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(contradiction,plain,
% 3.24/0.99      ( $false ),
% 3.24/0.99      inference(minisat,[status(thm)],[c_8073,c_823,c_460,c_36,c_14,c_16]) ).
% 3.24/0.99  
% 3.24/0.99  
% 3.24/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.24/0.99  
% 3.24/0.99  ------                               Statistics
% 3.24/0.99  
% 3.24/0.99  ------ Selected
% 3.24/0.99  
% 3.24/0.99  total_time:                             0.249
% 3.24/0.99  
%------------------------------------------------------------------------------
