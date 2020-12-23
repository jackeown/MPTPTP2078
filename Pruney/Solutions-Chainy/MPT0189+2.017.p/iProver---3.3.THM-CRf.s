%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:27:53 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 106 expanded)
%              Number of clauses        :   24 (  27 expanded)
%              Number of leaves         :   10 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 ( 131 expanded)
%              Number of equality atoms :   68 ( 130 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f19,f27])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)) ),
    inference(definition_unfolding,[],[f20,f27,f28])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X3,X2)) ),
    inference(definition_unfolding,[],[f17,f28,f28])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X3,X2,X1)) ),
    inference(definition_unfolding,[],[f18,f28,f28])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) ),
    inference(ennf_transformation,[],[f12])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f14])).

fof(f26,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f34,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK2,sK3)) ),
    inference(definition_unfolding,[],[f26,f28,f28])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_20,plain,
    ( k2_xboole_0(X0_35,X1_35) = k2_xboole_0(X1_35,X0_35) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1215,plain,
    ( k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK3,sK2)) = k2_xboole_0(k1_enumset1(sK0,sK3,sK2),k1_enumset1(sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_23,plain,
    ( X0_35 != X1_35
    | X2_35 != X1_35
    | X2_35 = X0_35 ),
    theory(equality)).

cnf(c_88,plain,
    ( X0_35 != X1_35
    | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != X1_35
    | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) = X0_35 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_660,plain,
    ( X0_35 != k2_xboole_0(k1_enumset1(sK0,sK3,sK2),k1_enumset1(sK1,sK1,sK1))
    | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) = X0_35
    | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK3,sK2),k1_enumset1(sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_88])).

cnf(c_1214,plain,
    ( k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK3,sK2)) != k2_xboole_0(k1_enumset1(sK0,sK3,sK2),k1_enumset1(sK1,sK1,sK1))
    | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) = k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK3,sK2))
    | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK3,sK2),k1_enumset1(sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_660])).

cnf(c_4,plain,
    ( k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_17,plain,
    ( k2_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X3_36,X3_36,X3_36)) = k2_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X2_36,X3_36)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_330,plain,
    ( k2_xboole_0(k1_enumset1(sK0,sK3,sK2),k1_enumset1(sK1,sK1,sK1)) = k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK3,sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_152,plain,
    ( X0_35 != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK3,sK2,sK1))
    | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) = X0_35
    | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK3,sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_88])).

cnf(c_329,plain,
    ( k2_xboole_0(k1_enumset1(sK0,sK3,sK2),k1_enumset1(sK1,sK1,sK1)) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK3,sK2,sK1))
    | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) = k2_xboole_0(k1_enumset1(sK0,sK3,sK2),k1_enumset1(sK1,sK1,sK1))
    | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK3,sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_152])).

cnf(c_2,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X3,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_19,plain,
    ( k2_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X2_36,X3_36)) = k2_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X3_36,X2_36)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_163,plain,
    ( k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK2,sK3)) = k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_54,plain,
    ( k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK2,sK3)) != X0_35
    | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != X0_35
    | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) = k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_89,plain,
    ( k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK2,sK3)) != k2_xboole_0(X0_35,X1_35)
    | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(X0_35,X1_35)
    | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) = k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_162,plain,
    ( k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK3,sK2))
    | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK3,sK2))
    | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) = k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_89])).

cnf(c_3,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X3,X2,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_18,plain,
    ( k2_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X2_36,X3_36)) = k2_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X3_36,X2_36,X1_36)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_81,plain,
    ( k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) = k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK3,sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_6,negated_conjecture,
    ( k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_15,negated_conjecture,
    ( k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1215,c_1214,c_330,c_329,c_163,c_162,c_81,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:16:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.17/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/0.98  
% 2.17/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.17/0.98  
% 2.17/0.98  ------  iProver source info
% 2.17/0.98  
% 2.17/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.17/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.17/0.98  git: non_committed_changes: false
% 2.17/0.98  git: last_make_outside_of_git: false
% 2.17/0.98  
% 2.17/0.98  ------ 
% 2.17/0.98  ------ Parsing...
% 2.17/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.17/0.98  
% 2.17/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.17/0.98  
% 2.17/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.17/0.98  
% 2.17/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.17/0.98  ------ Proving...
% 2.17/0.98  ------ Problem Properties 
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  clauses                                 7
% 2.17/0.98  conjectures                             1
% 2.17/0.98  EPR                                     0
% 2.17/0.98  Horn                                    7
% 2.17/0.98  unary                                   7
% 2.17/0.98  binary                                  0
% 2.17/0.98  lits                                    7
% 2.17/0.98  lits eq                                 7
% 2.17/0.98  fd_pure                                 0
% 2.17/0.98  fd_pseudo                               0
% 2.17/0.98  fd_cond                                 0
% 2.17/0.98  fd_pseudo_cond                          0
% 2.17/0.98  AC symbols                              0
% 2.17/0.98  
% 2.17/0.98  ------ Input Options Time Limit: Unbounded
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  ------ 
% 2.17/0.98  Current options:
% 2.17/0.98  ------ 
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  ------ Proving...
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  % SZS status Theorem for theBenchmark.p
% 2.17/0.98  
% 2.17/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.17/0.98  
% 2.17/0.98  fof(f1,axiom,(
% 2.17/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f16,plain,(
% 2.17/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f1])).
% 2.17/0.98  
% 2.17/0.98  fof(f5,axiom,(
% 2.17/0.98    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)),
% 2.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f20,plain,(
% 2.17/0.98    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f5])).
% 2.17/0.98  
% 2.17/0.98  fof(f4,axiom,(
% 2.17/0.98    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 2.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f19,plain,(
% 2.17/0.98    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f4])).
% 2.17/0.98  
% 2.17/0.98  fof(f6,axiom,(
% 2.17/0.98    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f21,plain,(
% 2.17/0.98    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f6])).
% 2.17/0.98  
% 2.17/0.98  fof(f7,axiom,(
% 2.17/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f22,plain,(
% 2.17/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f7])).
% 2.17/0.98  
% 2.17/0.98  fof(f27,plain,(
% 2.17/0.98    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 2.17/0.98    inference(definition_unfolding,[],[f21,f22])).
% 2.17/0.98  
% 2.17/0.98  fof(f28,plain,(
% 2.17/0.98    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.17/0.98    inference(definition_unfolding,[],[f19,f27])).
% 2.17/0.98  
% 2.17/0.98  fof(f32,plain,(
% 2.17/0.98    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) )),
% 2.17/0.98    inference(definition_unfolding,[],[f20,f27,f28])).
% 2.17/0.98  
% 2.17/0.98  fof(f2,axiom,(
% 2.17/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 2.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f17,plain,(
% 2.17/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f2])).
% 2.17/0.98  
% 2.17/0.98  fof(f30,plain,(
% 2.17/0.98    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X3,X2))) )),
% 2.17/0.98    inference(definition_unfolding,[],[f17,f28,f28])).
% 2.17/0.98  
% 2.17/0.98  fof(f3,axiom,(
% 2.17/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 2.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f18,plain,(
% 2.17/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 2.17/0.98    inference(cnf_transformation,[],[f3])).
% 2.17/0.98  
% 2.17/0.98  fof(f31,plain,(
% 2.17/0.98    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X3,X2,X1))) )),
% 2.17/0.98    inference(definition_unfolding,[],[f18,f28,f28])).
% 2.17/0.98  
% 2.17/0.98  fof(f11,conjecture,(
% 2.17/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 2.17/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.98  
% 2.17/0.98  fof(f12,negated_conjecture,(
% 2.17/0.98    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 2.17/0.98    inference(negated_conjecture,[],[f11])).
% 2.17/0.98  
% 2.17/0.98  fof(f13,plain,(
% 2.17/0.98    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 2.17/0.98    inference(ennf_transformation,[],[f12])).
% 2.17/0.98  
% 2.17/0.98  fof(f14,plain,(
% 2.17/0.98    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 2.17/0.98    introduced(choice_axiom,[])).
% 2.17/0.98  
% 2.17/0.98  fof(f15,plain,(
% 2.17/0.98    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 2.17/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f14])).
% 2.17/0.98  
% 2.17/0.98  fof(f26,plain,(
% 2.17/0.98    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 2.17/0.98    inference(cnf_transformation,[],[f15])).
% 2.17/0.98  
% 2.17/0.98  fof(f34,plain,(
% 2.17/0.98    k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK2,sK3))),
% 2.17/0.98    inference(definition_unfolding,[],[f26,f28,f28])).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1,plain,
% 2.17/0.98      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 2.17/0.98      inference(cnf_transformation,[],[f16]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_20,plain,
% 2.17/0.98      ( k2_xboole_0(X0_35,X1_35) = k2_xboole_0(X1_35,X0_35) ),
% 2.17/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1215,plain,
% 2.17/0.98      ( k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK3,sK2)) = k2_xboole_0(k1_enumset1(sK0,sK3,sK2),k1_enumset1(sK1,sK1,sK1)) ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_20]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_23,plain,
% 2.17/0.98      ( X0_35 != X1_35 | X2_35 != X1_35 | X2_35 = X0_35 ),
% 2.17/0.98      theory(equality) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_88,plain,
% 2.17/0.98      ( X0_35 != X1_35
% 2.17/0.98      | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != X1_35
% 2.17/0.98      | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) = X0_35 ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_23]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_660,plain,
% 2.17/0.98      ( X0_35 != k2_xboole_0(k1_enumset1(sK0,sK3,sK2),k1_enumset1(sK1,sK1,sK1))
% 2.17/0.98      | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) = X0_35
% 2.17/0.98      | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK3,sK2),k1_enumset1(sK1,sK1,sK1)) ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_88]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_1214,plain,
% 2.17/0.98      ( k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK3,sK2)) != k2_xboole_0(k1_enumset1(sK0,sK3,sK2),k1_enumset1(sK1,sK1,sK1))
% 2.17/0.98      | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) = k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK3,sK2))
% 2.17/0.98      | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK3,sK2),k1_enumset1(sK1,sK1,sK1)) ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_660]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_4,plain,
% 2.17/0.98      ( k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) ),
% 2.17/0.98      inference(cnf_transformation,[],[f32]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_17,plain,
% 2.17/0.98      ( k2_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X3_36,X3_36,X3_36)) = k2_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X2_36,X3_36)) ),
% 2.17/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_330,plain,
% 2.17/0.98      ( k2_xboole_0(k1_enumset1(sK0,sK3,sK2),k1_enumset1(sK1,sK1,sK1)) = k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK3,sK2,sK1)) ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_17]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_152,plain,
% 2.17/0.98      ( X0_35 != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK3,sK2,sK1))
% 2.17/0.98      | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) = X0_35
% 2.17/0.98      | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK3,sK2,sK1)) ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_88]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_329,plain,
% 2.17/0.98      ( k2_xboole_0(k1_enumset1(sK0,sK3,sK2),k1_enumset1(sK1,sK1,sK1)) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK3,sK2,sK1))
% 2.17/0.98      | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) = k2_xboole_0(k1_enumset1(sK0,sK3,sK2),k1_enumset1(sK1,sK1,sK1))
% 2.17/0.98      | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK3,sK2,sK1)) ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_152]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_2,plain,
% 2.17/0.98      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X3,X2)) ),
% 2.17/0.98      inference(cnf_transformation,[],[f30]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_19,plain,
% 2.17/0.98      ( k2_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X2_36,X3_36)) = k2_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X3_36,X2_36)) ),
% 2.17/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_163,plain,
% 2.17/0.98      ( k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK2,sK3)) = k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK3,sK2)) ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_19]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_54,plain,
% 2.17/0.98      ( k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK2,sK3)) != X0_35
% 2.17/0.98      | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != X0_35
% 2.17/0.98      | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) = k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK2,sK3)) ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_23]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_89,plain,
% 2.17/0.98      ( k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK2,sK3)) != k2_xboole_0(X0_35,X1_35)
% 2.17/0.98      | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(X0_35,X1_35)
% 2.17/0.98      | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) = k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK2,sK3)) ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_54]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_162,plain,
% 2.17/0.98      ( k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK3,sK2))
% 2.17/0.98      | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK3,sK2))
% 2.17/0.98      | k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) = k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK2,sK3)) ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_89]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_3,plain,
% 2.17/0.98      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X3,X2,X1)) ),
% 2.17/0.98      inference(cnf_transformation,[],[f31]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_18,plain,
% 2.17/0.98      ( k2_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X1_36,X2_36,X3_36)) = k2_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k1_enumset1(X3_36,X2_36,X1_36)) ),
% 2.17/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_81,plain,
% 2.17/0.98      ( k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) = k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK3,sK2,sK1)) ),
% 2.17/0.98      inference(instantiation,[status(thm)],[c_18]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_6,negated_conjecture,
% 2.17/0.98      ( k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK2,sK3)) ),
% 2.17/0.98      inference(cnf_transformation,[],[f34]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(c_15,negated_conjecture,
% 2.17/0.98      ( k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK2,sK3)) ),
% 2.17/0.98      inference(subtyping,[status(esa)],[c_6]) ).
% 2.17/0.98  
% 2.17/0.98  cnf(contradiction,plain,
% 2.17/0.98      ( $false ),
% 2.17/0.98      inference(minisat,
% 2.17/0.98                [status(thm)],
% 2.17/0.98                [c_1215,c_1214,c_330,c_329,c_163,c_162,c_81,c_15]) ).
% 2.17/0.98  
% 2.17/0.98  
% 2.17/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.17/0.98  
% 2.17/0.98  ------                               Statistics
% 2.17/0.98  
% 2.17/0.98  ------ Selected
% 2.17/0.98  
% 2.17/0.98  total_time:                             0.126
% 2.17/0.98  
%------------------------------------------------------------------------------
