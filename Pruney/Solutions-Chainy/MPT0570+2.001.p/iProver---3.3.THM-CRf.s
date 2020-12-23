%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:34 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 103 expanded)
%              Number of clauses        :   32 (  33 expanded)
%              Number of leaves         :   14 (  23 expanded)
%              Depth                    :   14
%              Number of atoms          :  166 ( 258 expanded)
%              Number of equality atoms :   74 ( 124 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

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

fof(f31,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f40,f37])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

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

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f34,f37])).

fof(f43,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,(
    k1_xboole_0 = k10_relat_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f44,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_360,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK2,k2_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_351,plain,
    ( r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_355,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1114,plain,
    ( k4_xboole_0(sK2,k2_relat_1(sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_351,c_355])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1216,plain,
    ( k1_setfam_1(k2_tarski(sK2,k2_relat_1(sK3))) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1114,c_9])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1217,plain,
    ( k1_setfam_1(k2_tarski(sK2,k2_relat_1(sK3))) = sK2 ),
    inference(demodulation,[status(thm)],[c_1216,c_6])).

cnf(c_8,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_357,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_400,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_357,c_9])).

cnf(c_3836,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k1_setfam_1(k2_tarski(X1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_400])).

cnf(c_5222,plain,
    ( r1_xboole_0(k2_relat_1(sK3),sK2) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1217,c_3836])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_16,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

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

cnf(c_712,plain,
    ( r1_xboole_0(k2_relat_1(sK3),sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_352])).

cnf(c_5629,plain,
    ( r2_hidden(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5222,c_16,c_712])).

cnf(c_5636,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_360,c_5629])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_458,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_459,plain,
    ( k1_xboole_0 = sK2
    | v1_xboole_0(sK2) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_458])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_37,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f44])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5636,c_459,c_37,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:32:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.77/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.01  
% 2.77/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.77/1.01  
% 2.77/1.01  ------  iProver source info
% 2.77/1.01  
% 2.77/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.77/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.77/1.01  git: non_committed_changes: false
% 2.77/1.01  git: last_make_outside_of_git: false
% 2.77/1.01  
% 2.77/1.01  ------ 
% 2.77/1.01  ------ Parsing...
% 2.77/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.77/1.01  
% 2.77/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 2.77/1.01  
% 2.77/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.77/1.01  
% 2.77/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.77/1.01  ------ Proving...
% 2.77/1.01  ------ Problem Properties 
% 2.77/1.01  
% 2.77/1.01  
% 2.77/1.01  clauses                                 16
% 2.77/1.01  conjectures                             4
% 2.77/1.01  EPR                                     5
% 2.77/1.01  Horn                                    14
% 2.77/1.01  unary                                   8
% 2.77/1.01  binary                                  5
% 2.77/1.01  lits                                    27
% 2.77/1.01  lits eq                                 9
% 2.77/1.01  fd_pure                                 0
% 2.77/1.01  fd_pseudo                               0
% 2.77/1.01  fd_cond                                 0
% 2.77/1.01  fd_pseudo_cond                          1
% 2.77/1.01  AC symbols                              0
% 2.77/1.01  
% 2.77/1.01  ------ Input Options Time Limit: Unbounded
% 2.77/1.01  
% 2.77/1.01  
% 2.77/1.01  ------ 
% 2.77/1.01  Current options:
% 2.77/1.01  ------ 
% 2.77/1.01  
% 2.77/1.01  
% 2.77/1.01  
% 2.77/1.01  
% 2.77/1.01  ------ Proving...
% 2.77/1.01  
% 2.77/1.01  
% 2.77/1.01  % SZS status Theorem for theBenchmark.p
% 2.77/1.01  
% 2.77/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.77/1.01  
% 2.77/1.01  fof(f1,axiom,(
% 2.77/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.77/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.01  
% 2.77/1.01  fof(f21,plain,(
% 2.77/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.77/1.01    inference(nnf_transformation,[],[f1])).
% 2.77/1.01  
% 2.77/1.01  fof(f22,plain,(
% 2.77/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.77/1.01    inference(rectify,[],[f21])).
% 2.77/1.01  
% 2.77/1.01  fof(f23,plain,(
% 2.77/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.77/1.01    introduced(choice_axiom,[])).
% 2.77/1.01  
% 2.77/1.01  fof(f24,plain,(
% 2.77/1.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.77/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 2.77/1.01  
% 2.77/1.01  fof(f31,plain,(
% 2.77/1.01    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.77/1.01    inference(cnf_transformation,[],[f24])).
% 2.77/1.01  
% 2.77/1.01  fof(f11,conjecture,(
% 2.77/1.01    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 2.77/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.01  
% 2.77/1.01  fof(f12,negated_conjecture,(
% 2.77/1.01    ~! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 2.77/1.01    inference(negated_conjecture,[],[f11])).
% 2.77/1.01  
% 2.77/1.01  fof(f19,plain,(
% 2.77/1.01    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 2.77/1.01    inference(ennf_transformation,[],[f12])).
% 2.77/1.01  
% 2.77/1.01  fof(f20,plain,(
% 2.77/1.01    ? [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 2.77/1.01    inference(flattening,[],[f19])).
% 2.77/1.01  
% 2.77/1.01  fof(f28,plain,(
% 2.77/1.01    ? [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1)) => (k1_xboole_0 = k10_relat_1(sK3,sK2) & r1_tarski(sK2,k2_relat_1(sK3)) & k1_xboole_0 != sK2 & v1_relat_1(sK3))),
% 2.77/1.01    introduced(choice_axiom,[])).
% 2.77/1.01  
% 2.77/1.01  fof(f29,plain,(
% 2.77/1.01    k1_xboole_0 = k10_relat_1(sK3,sK2) & r1_tarski(sK2,k2_relat_1(sK3)) & k1_xboole_0 != sK2 & v1_relat_1(sK3)),
% 2.77/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f28])).
% 2.77/1.01  
% 2.77/1.01  fof(f45,plain,(
% 2.77/1.01    r1_tarski(sK2,k2_relat_1(sK3))),
% 2.77/1.01    inference(cnf_transformation,[],[f29])).
% 2.77/1.01  
% 2.77/1.01  fof(f4,axiom,(
% 2.77/1.01    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.77/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.01  
% 2.77/1.01  fof(f14,plain,(
% 2.77/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 2.77/1.01    inference(unused_predicate_definition_removal,[],[f4])).
% 2.77/1.01  
% 2.77/1.01  fof(f16,plain,(
% 2.77/1.01    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 2.77/1.01    inference(ennf_transformation,[],[f14])).
% 2.77/1.01  
% 2.77/1.01  fof(f35,plain,(
% 2.77/1.01    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 2.77/1.01    inference(cnf_transformation,[],[f16])).
% 2.77/1.01  
% 2.77/1.01  fof(f9,axiom,(
% 2.77/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.77/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.01  
% 2.77/1.01  fof(f40,plain,(
% 2.77/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.77/1.01    inference(cnf_transformation,[],[f9])).
% 2.77/1.01  
% 2.77/1.01  fof(f6,axiom,(
% 2.77/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.77/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.01  
% 2.77/1.01  fof(f37,plain,(
% 2.77/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.77/1.01    inference(cnf_transformation,[],[f6])).
% 2.77/1.01  
% 2.77/1.01  fof(f49,plain,(
% 2.77/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.77/1.01    inference(definition_unfolding,[],[f40,f37])).
% 2.77/1.01  
% 2.77/1.01  fof(f5,axiom,(
% 2.77/1.01    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.77/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.01  
% 2.77/1.01  fof(f36,plain,(
% 2.77/1.01    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.77/1.01    inference(cnf_transformation,[],[f5])).
% 2.77/1.01  
% 2.77/1.01  fof(f8,axiom,(
% 2.77/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.77/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.01  
% 2.77/1.01  fof(f39,plain,(
% 2.77/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.77/1.01    inference(cnf_transformation,[],[f8])).
% 2.77/1.01  
% 2.77/1.01  fof(f3,axiom,(
% 2.77/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.77/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.01  
% 2.77/1.01  fof(f13,plain,(
% 2.77/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.77/1.01    inference(rectify,[],[f3])).
% 2.77/1.01  
% 2.77/1.01  fof(f15,plain,(
% 2.77/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.77/1.01    inference(ennf_transformation,[],[f13])).
% 2.77/1.01  
% 2.77/1.01  fof(f25,plain,(
% 2.77/1.01    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 2.77/1.01    introduced(choice_axiom,[])).
% 2.77/1.01  
% 2.77/1.01  fof(f26,plain,(
% 2.77/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.77/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f25])).
% 2.77/1.01  
% 2.77/1.01  fof(f34,plain,(
% 2.77/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.77/1.01    inference(cnf_transformation,[],[f26])).
% 2.77/1.01  
% 2.77/1.01  fof(f47,plain,(
% 2.77/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.77/1.01    inference(definition_unfolding,[],[f34,f37])).
% 2.77/1.01  
% 2.77/1.01  fof(f43,plain,(
% 2.77/1.01    v1_relat_1(sK3)),
% 2.77/1.01    inference(cnf_transformation,[],[f29])).
% 2.77/1.01  
% 2.77/1.01  fof(f46,plain,(
% 2.77/1.01    k1_xboole_0 = k10_relat_1(sK3,sK2)),
% 2.77/1.01    inference(cnf_transformation,[],[f29])).
% 2.77/1.01  
% 2.77/1.01  fof(f10,axiom,(
% 2.77/1.01    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 2.77/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.01  
% 2.77/1.01  fof(f18,plain,(
% 2.77/1.01    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.77/1.01    inference(ennf_transformation,[],[f10])).
% 2.77/1.01  
% 2.77/1.01  fof(f27,plain,(
% 2.77/1.01    ! [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.77/1.01    inference(nnf_transformation,[],[f18])).
% 2.77/1.01  
% 2.77/1.01  fof(f41,plain,(
% 2.77/1.01    ( ! [X0,X1] : (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.77/1.01    inference(cnf_transformation,[],[f27])).
% 2.77/1.01  
% 2.77/1.01  fof(f7,axiom,(
% 2.77/1.01    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.77/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.01  
% 2.77/1.01  fof(f17,plain,(
% 2.77/1.01    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.77/1.01    inference(ennf_transformation,[],[f7])).
% 2.77/1.01  
% 2.77/1.01  fof(f38,plain,(
% 2.77/1.01    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.77/1.01    inference(cnf_transformation,[],[f17])).
% 2.77/1.01  
% 2.77/1.01  fof(f2,axiom,(
% 2.77/1.01    v1_xboole_0(k1_xboole_0)),
% 2.77/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.01  
% 2.77/1.01  fof(f32,plain,(
% 2.77/1.01    v1_xboole_0(k1_xboole_0)),
% 2.77/1.01    inference(cnf_transformation,[],[f2])).
% 2.77/1.01  
% 2.77/1.01  fof(f44,plain,(
% 2.77/1.01    k1_xboole_0 != sK2),
% 2.77/1.01    inference(cnf_transformation,[],[f29])).
% 2.77/1.01  
% 2.77/1.01  cnf(c_0,plain,
% 2.77/1.01      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.77/1.01      inference(cnf_transformation,[],[f31]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(c_360,plain,
% 2.77/1.01      ( r2_hidden(sK0(X0),X0) = iProver_top
% 2.77/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.77/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(c_13,negated_conjecture,
% 2.77/1.01      ( r1_tarski(sK2,k2_relat_1(sK3)) ),
% 2.77/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(c_351,plain,
% 2.77/1.01      ( r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top ),
% 2.77/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(c_5,plain,
% 2.77/1.01      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 2.77/1.01      inference(cnf_transformation,[],[f35]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(c_355,plain,
% 2.77/1.01      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 2.77/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 2.77/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(c_1114,plain,
% 2.77/1.01      ( k4_xboole_0(sK2,k2_relat_1(sK3)) = k1_xboole_0 ),
% 2.77/1.01      inference(superposition,[status(thm)],[c_351,c_355]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(c_9,plain,
% 2.77/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 2.77/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(c_1216,plain,
% 2.77/1.01      ( k1_setfam_1(k2_tarski(sK2,k2_relat_1(sK3))) = k4_xboole_0(sK2,k1_xboole_0) ),
% 2.77/1.01      inference(superposition,[status(thm)],[c_1114,c_9]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(c_6,plain,
% 2.77/1.01      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.77/1.01      inference(cnf_transformation,[],[f36]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(c_1217,plain,
% 2.77/1.01      ( k1_setfam_1(k2_tarski(sK2,k2_relat_1(sK3))) = sK2 ),
% 2.77/1.01      inference(demodulation,[status(thm)],[c_1216,c_6]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(c_8,plain,
% 2.77/1.01      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 2.77/1.01      inference(cnf_transformation,[],[f39]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(c_3,plain,
% 2.77/1.01      ( ~ r1_xboole_0(X0,X1)
% 2.77/1.01      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 2.77/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(c_357,plain,
% 2.77/1.01      ( r1_xboole_0(X0,X1) != iProver_top
% 2.77/1.01      | r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) != iProver_top ),
% 2.77/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(c_400,plain,
% 2.77/1.01      ( r1_xboole_0(X0,X1) != iProver_top
% 2.77/1.01      | r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) != iProver_top ),
% 2.77/1.01      inference(light_normalisation,[status(thm)],[c_357,c_9]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(c_3836,plain,
% 2.77/1.01      ( r1_xboole_0(X0,X1) != iProver_top
% 2.77/1.01      | r2_hidden(X2,k1_setfam_1(k2_tarski(X1,X0))) != iProver_top ),
% 2.77/1.01      inference(superposition,[status(thm)],[c_8,c_400]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(c_5222,plain,
% 2.77/1.01      ( r1_xboole_0(k2_relat_1(sK3),sK2) != iProver_top
% 2.77/1.01      | r2_hidden(X0,sK2) != iProver_top ),
% 2.77/1.01      inference(superposition,[status(thm)],[c_1217,c_3836]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(c_15,negated_conjecture,
% 2.77/1.01      ( v1_relat_1(sK3) ),
% 2.77/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(c_16,plain,
% 2.77/1.01      ( v1_relat_1(sK3) = iProver_top ),
% 2.77/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(c_12,negated_conjecture,
% 2.77/1.01      ( k1_xboole_0 = k10_relat_1(sK3,sK2) ),
% 2.77/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(c_11,plain,
% 2.77/1.01      ( r1_xboole_0(k2_relat_1(X0),X1)
% 2.77/1.01      | ~ v1_relat_1(X0)
% 2.77/1.01      | k10_relat_1(X0,X1) != k1_xboole_0 ),
% 2.77/1.01      inference(cnf_transformation,[],[f41]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(c_352,plain,
% 2.77/1.01      ( k10_relat_1(X0,X1) != k1_xboole_0
% 2.77/1.01      | r1_xboole_0(k2_relat_1(X0),X1) = iProver_top
% 2.77/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.77/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(c_712,plain,
% 2.77/1.01      ( r1_xboole_0(k2_relat_1(sK3),sK2) = iProver_top
% 2.77/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.77/1.01      inference(superposition,[status(thm)],[c_12,c_352]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(c_5629,plain,
% 2.77/1.01      ( r2_hidden(X0,sK2) != iProver_top ),
% 2.77/1.01      inference(global_propositional_subsumption,
% 2.77/1.01                [status(thm)],
% 2.77/1.01                [c_5222,c_16,c_712]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(c_5636,plain,
% 2.77/1.01      ( v1_xboole_0(sK2) = iProver_top ),
% 2.77/1.01      inference(superposition,[status(thm)],[c_360,c_5629]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(c_7,plain,
% 2.77/1.01      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 2.77/1.01      inference(cnf_transformation,[],[f38]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(c_458,plain,
% 2.77/1.01      ( ~ v1_xboole_0(sK2)
% 2.77/1.01      | ~ v1_xboole_0(k1_xboole_0)
% 2.77/1.01      | k1_xboole_0 = sK2 ),
% 2.77/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(c_459,plain,
% 2.77/1.01      ( k1_xboole_0 = sK2
% 2.77/1.01      | v1_xboole_0(sK2) != iProver_top
% 2.77/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.77/1.01      inference(predicate_to_equality,[status(thm)],[c_458]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(c_2,plain,
% 2.77/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 2.77/1.01      inference(cnf_transformation,[],[f32]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(c_37,plain,
% 2.77/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.77/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(c_14,negated_conjecture,
% 2.77/1.01      ( k1_xboole_0 != sK2 ),
% 2.77/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.77/1.01  
% 2.77/1.01  cnf(contradiction,plain,
% 2.77/1.01      ( $false ),
% 2.77/1.01      inference(minisat,[status(thm)],[c_5636,c_459,c_37,c_14]) ).
% 2.77/1.01  
% 2.77/1.01  
% 2.77/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.77/1.01  
% 2.77/1.01  ------                               Statistics
% 2.77/1.01  
% 2.77/1.01  ------ Selected
% 2.77/1.01  
% 2.77/1.01  total_time:                             0.217
% 2.77/1.01  
%------------------------------------------------------------------------------
