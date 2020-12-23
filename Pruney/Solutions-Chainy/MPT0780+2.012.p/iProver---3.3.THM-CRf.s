%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:23 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   60 (  96 expanded)
%              Number of clauses        :   27 (  31 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 177 expanded)
%              Number of equality atoms :   55 (  93 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f17])).

fof(f28,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f22,f24])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f20,f24])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X0,X2))) = k1_setfam_1(k2_tarski(X0,k2_xboole_0(X1,X2))) ),
    inference(definition_unfolding,[],[f23,f24,f24,f24])).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f25,f24])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f29,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_194,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_198,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_516,plain,
    ( k2_xboole_0(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_194,c_198])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_3,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_197,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_515,plain,
    ( k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X0) = X0 ),
    inference(superposition,[status(thm)],[c_197,c_198])).

cnf(c_1,plain,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_4,plain,
    ( k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X0,X2))) = k1_setfam_1(k2_tarski(X0,k2_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_611,plain,
    ( k1_setfam_1(k2_tarski(X0,k2_xboole_0(X1,X0))) = k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_1,c_4])).

cnf(c_1105,plain,
    ( k1_setfam_1(k2_tarski(X0,k2_xboole_0(X1,X0))) = X0 ),
    inference(demodulation,[status(thm)],[c_515,c_611])).

cnf(c_1225,plain,
    ( k1_setfam_1(k2_tarski(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_1105])).

cnf(c_1418,plain,
    ( k1_setfam_1(k2_tarski(sK0,sK1)) = sK0 ),
    inference(superposition,[status(thm)],[c_516,c_1225])).

cnf(c_9,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_193,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_wellord1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k2_wellord1(k2_wellord1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_196,plain,
    ( k2_wellord1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k2_wellord1(k2_wellord1(X0,X1),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1411,plain,
    ( k2_wellord1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k2_wellord1(k2_wellord1(sK2,X0),X1) ),
    inference(superposition,[status(thm)],[c_193,c_196])).

cnf(c_1905,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k2_wellord1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_1418,c_1411])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(k2_wellord1(X0,X2),X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_195,plain,
    ( k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(k2_wellord1(X0,X2),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_605,plain,
    ( k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(k2_wellord1(sK2,X1),X0) ),
    inference(superposition,[status(thm)],[c_193,c_195])).

cnf(c_7,negated_conjecture,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_909,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_605,c_7])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1905,c_909])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.33/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.02  
% 3.33/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.33/1.02  
% 3.33/1.02  ------  iProver source info
% 3.33/1.02  
% 3.33/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.33/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.33/1.02  git: non_committed_changes: false
% 3.33/1.02  git: last_make_outside_of_git: false
% 3.33/1.02  
% 3.33/1.02  ------ 
% 3.33/1.02  ------ Parsing...
% 3.33/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.33/1.02  
% 3.33/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.33/1.02  
% 3.33/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.33/1.02  
% 3.33/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.33/1.02  ------ Proving...
% 3.33/1.02  ------ Problem Properties 
% 3.33/1.02  
% 3.33/1.02  
% 3.33/1.02  clauses                                 10
% 3.33/1.02  conjectures                             3
% 3.33/1.02  EPR                                     2
% 3.33/1.02  Horn                                    10
% 3.33/1.02  unary                                   7
% 3.33/1.02  binary                                  3
% 3.33/1.02  lits                                    13
% 3.33/1.02  lits eq                                 7
% 3.33/1.02  fd_pure                                 0
% 3.33/1.02  fd_pseudo                               0
% 3.33/1.02  fd_cond                                 0
% 3.33/1.02  fd_pseudo_cond                          0
% 3.33/1.02  AC symbols                              0
% 3.33/1.02  
% 3.33/1.02  ------ Input Options Time Limit: Unbounded
% 3.33/1.02  
% 3.33/1.02  
% 3.33/1.02  ------ 
% 3.33/1.02  Current options:
% 3.33/1.02  ------ 
% 3.33/1.02  
% 3.33/1.02  
% 3.33/1.02  
% 3.33/1.02  
% 3.33/1.02  ------ Proving...
% 3.33/1.02  
% 3.33/1.02  
% 3.33/1.02  % SZS status Theorem for theBenchmark.p
% 3.33/1.02  
% 3.33/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.33/1.02  
% 3.33/1.02  fof(f9,conjecture,(
% 3.33/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 3.33/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.02  
% 3.33/1.02  fof(f10,negated_conjecture,(
% 3.33/1.02    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 3.33/1.02    inference(negated_conjecture,[],[f9])).
% 3.33/1.02  
% 3.33/1.02  fof(f15,plain,(
% 3.33/1.02    ? [X0,X1,X2] : ((k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 3.33/1.02    inference(ennf_transformation,[],[f10])).
% 3.33/1.02  
% 3.33/1.02  fof(f16,plain,(
% 3.33/1.02    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 3.33/1.02    inference(flattening,[],[f15])).
% 3.33/1.02  
% 3.33/1.02  fof(f17,plain,(
% 3.33/1.02    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 3.33/1.02    introduced(choice_axiom,[])).
% 3.33/1.02  
% 3.33/1.02  fof(f18,plain,(
% 3.33/1.02    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 3.33/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f17])).
% 3.33/1.02  
% 3.33/1.02  fof(f28,plain,(
% 3.33/1.02    r1_tarski(sK0,sK1)),
% 3.33/1.02    inference(cnf_transformation,[],[f18])).
% 3.33/1.02  
% 3.33/1.02  fof(f3,axiom,(
% 3.33/1.02    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.33/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.02  
% 3.33/1.02  fof(f12,plain,(
% 3.33/1.02    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.33/1.02    inference(ennf_transformation,[],[f3])).
% 3.33/1.02  
% 3.33/1.02  fof(f21,plain,(
% 3.33/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.33/1.02    inference(cnf_transformation,[],[f12])).
% 3.33/1.02  
% 3.33/1.02  fof(f1,axiom,(
% 3.33/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.33/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.02  
% 3.33/1.02  fof(f19,plain,(
% 3.33/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.33/1.02    inference(cnf_transformation,[],[f1])).
% 3.33/1.02  
% 3.33/1.02  fof(f4,axiom,(
% 3.33/1.02    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.33/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.02  
% 3.33/1.02  fof(f22,plain,(
% 3.33/1.02    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.33/1.02    inference(cnf_transformation,[],[f4])).
% 3.33/1.02  
% 3.33/1.02  fof(f6,axiom,(
% 3.33/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.33/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.02  
% 3.33/1.02  fof(f24,plain,(
% 3.33/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.33/1.02    inference(cnf_transformation,[],[f6])).
% 3.33/1.02  
% 3.33/1.02  fof(f31,plain,(
% 3.33/1.02    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 3.33/1.02    inference(definition_unfolding,[],[f22,f24])).
% 3.33/1.02  
% 3.33/1.02  fof(f2,axiom,(
% 3.33/1.02    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.33/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.02  
% 3.33/1.02  fof(f11,plain,(
% 3.33/1.02    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.33/1.02    inference(rectify,[],[f2])).
% 3.33/1.02  
% 3.33/1.02  fof(f20,plain,(
% 3.33/1.02    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.33/1.02    inference(cnf_transformation,[],[f11])).
% 3.33/1.02  
% 3.33/1.02  fof(f30,plain,(
% 3.33/1.02    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 3.33/1.02    inference(definition_unfolding,[],[f20,f24])).
% 3.33/1.02  
% 3.33/1.02  fof(f5,axiom,(
% 3.33/1.02    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.33/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.02  
% 3.33/1.02  fof(f23,plain,(
% 3.33/1.02    ( ! [X2,X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.33/1.02    inference(cnf_transformation,[],[f5])).
% 3.33/1.02  
% 3.33/1.02  fof(f32,plain,(
% 3.33/1.02    ( ! [X2,X0,X1] : (k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X0,X2))) = k1_setfam_1(k2_tarski(X0,k2_xboole_0(X1,X2)))) )),
% 3.33/1.02    inference(definition_unfolding,[],[f23,f24,f24,f24])).
% 3.33/1.02  
% 3.33/1.02  fof(f27,plain,(
% 3.33/1.02    v1_relat_1(sK2)),
% 3.33/1.02    inference(cnf_transformation,[],[f18])).
% 3.33/1.02  
% 3.33/1.02  fof(f7,axiom,(
% 3.33/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1))),
% 3.33/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.02  
% 3.33/1.02  fof(f13,plain,(
% 3.33/1.02    ! [X0,X1,X2] : (k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1) | ~v1_relat_1(X2))),
% 3.33/1.02    inference(ennf_transformation,[],[f7])).
% 3.33/1.02  
% 3.33/1.02  fof(f25,plain,(
% 3.33/1.02    ( ! [X2,X0,X1] : (k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 3.33/1.02    inference(cnf_transformation,[],[f13])).
% 3.33/1.02  
% 3.33/1.02  fof(f33,plain,(
% 3.33/1.02    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~v1_relat_1(X2)) )),
% 3.33/1.02    inference(definition_unfolding,[],[f25,f24])).
% 3.33/1.02  
% 3.33/1.02  fof(f8,axiom,(
% 3.33/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0))),
% 3.33/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/1.02  
% 3.33/1.02  fof(f14,plain,(
% 3.33/1.02    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2))),
% 3.33/1.03    inference(ennf_transformation,[],[f8])).
% 3.33/1.03  
% 3.33/1.03  fof(f26,plain,(
% 3.33/1.03    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2)) )),
% 3.33/1.03    inference(cnf_transformation,[],[f14])).
% 3.33/1.03  
% 3.33/1.03  fof(f29,plain,(
% 3.33/1.03    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)),
% 3.33/1.03    inference(cnf_transformation,[],[f18])).
% 3.33/1.03  
% 3.33/1.03  cnf(c_8,negated_conjecture,
% 3.33/1.03      ( r1_tarski(sK0,sK1) ),
% 3.33/1.03      inference(cnf_transformation,[],[f28]) ).
% 3.33/1.03  
% 3.33/1.03  cnf(c_194,plain,
% 3.33/1.03      ( r1_tarski(sK0,sK1) = iProver_top ),
% 3.33/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.33/1.03  
% 3.33/1.03  cnf(c_2,plain,
% 3.33/1.03      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 3.33/1.03      inference(cnf_transformation,[],[f21]) ).
% 3.33/1.03  
% 3.33/1.03  cnf(c_198,plain,
% 3.33/1.03      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 3.33/1.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.33/1.03  
% 3.33/1.03  cnf(c_516,plain,
% 3.33/1.03      ( k2_xboole_0(sK0,sK1) = sK1 ),
% 3.33/1.03      inference(superposition,[status(thm)],[c_194,c_198]) ).
% 3.33/1.03  
% 3.33/1.03  cnf(c_0,plain,
% 3.33/1.03      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 3.33/1.03      inference(cnf_transformation,[],[f19]) ).
% 3.33/1.03  
% 3.33/1.03  cnf(c_3,plain,
% 3.33/1.03      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
% 3.33/1.03      inference(cnf_transformation,[],[f31]) ).
% 3.33/1.03  
% 3.33/1.03  cnf(c_197,plain,
% 3.33/1.03      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
% 3.33/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.33/1.03  
% 3.33/1.03  cnf(c_515,plain,
% 3.33/1.03      ( k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X0) = X0 ),
% 3.33/1.03      inference(superposition,[status(thm)],[c_197,c_198]) ).
% 3.33/1.03  
% 3.33/1.03  cnf(c_1,plain,
% 3.33/1.03      ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
% 3.33/1.03      inference(cnf_transformation,[],[f30]) ).
% 3.33/1.03  
% 3.33/1.03  cnf(c_4,plain,
% 3.33/1.03      ( k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X0,X2))) = k1_setfam_1(k2_tarski(X0,k2_xboole_0(X1,X2))) ),
% 3.33/1.03      inference(cnf_transformation,[],[f32]) ).
% 3.33/1.03  
% 3.33/1.03  cnf(c_611,plain,
% 3.33/1.03      ( k1_setfam_1(k2_tarski(X0,k2_xboole_0(X1,X0))) = k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
% 3.33/1.03      inference(superposition,[status(thm)],[c_1,c_4]) ).
% 3.33/1.03  
% 3.33/1.03  cnf(c_1105,plain,
% 3.33/1.03      ( k1_setfam_1(k2_tarski(X0,k2_xboole_0(X1,X0))) = X0 ),
% 3.33/1.03      inference(demodulation,[status(thm)],[c_515,c_611]) ).
% 3.33/1.03  
% 3.33/1.03  cnf(c_1225,plain,
% 3.33/1.03      ( k1_setfam_1(k2_tarski(X0,k2_xboole_0(X0,X1))) = X0 ),
% 3.33/1.03      inference(superposition,[status(thm)],[c_0,c_1105]) ).
% 3.33/1.03  
% 3.33/1.03  cnf(c_1418,plain,
% 3.33/1.03      ( k1_setfam_1(k2_tarski(sK0,sK1)) = sK0 ),
% 3.33/1.03      inference(superposition,[status(thm)],[c_516,c_1225]) ).
% 3.33/1.03  
% 3.33/1.03  cnf(c_9,negated_conjecture,
% 3.33/1.03      ( v1_relat_1(sK2) ),
% 3.33/1.03      inference(cnf_transformation,[],[f27]) ).
% 3.33/1.03  
% 3.33/1.03  cnf(c_193,plain,
% 3.33/1.03      ( v1_relat_1(sK2) = iProver_top ),
% 3.33/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.33/1.03  
% 3.33/1.03  cnf(c_5,plain,
% 3.33/1.03      ( ~ v1_relat_1(X0)
% 3.33/1.03      | k2_wellord1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k2_wellord1(k2_wellord1(X0,X1),X2) ),
% 3.33/1.03      inference(cnf_transformation,[],[f33]) ).
% 3.33/1.03  
% 3.33/1.03  cnf(c_196,plain,
% 3.33/1.03      ( k2_wellord1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k2_wellord1(k2_wellord1(X0,X1),X2)
% 3.33/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.33/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.33/1.03  
% 3.33/1.03  cnf(c_1411,plain,
% 3.33/1.03      ( k2_wellord1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k2_wellord1(k2_wellord1(sK2,X0),X1) ),
% 3.33/1.03      inference(superposition,[status(thm)],[c_193,c_196]) ).
% 3.33/1.03  
% 3.33/1.03  cnf(c_1905,plain,
% 3.33/1.03      ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k2_wellord1(sK2,sK0) ),
% 3.33/1.03      inference(superposition,[status(thm)],[c_1418,c_1411]) ).
% 3.33/1.03  
% 3.33/1.03  cnf(c_6,plain,
% 3.33/1.03      ( ~ v1_relat_1(X0)
% 3.33/1.03      | k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(k2_wellord1(X0,X2),X1) ),
% 3.33/1.03      inference(cnf_transformation,[],[f26]) ).
% 3.33/1.03  
% 3.33/1.03  cnf(c_195,plain,
% 3.33/1.03      ( k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(k2_wellord1(X0,X2),X1)
% 3.33/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.33/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.33/1.03  
% 3.33/1.03  cnf(c_605,plain,
% 3.33/1.03      ( k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(k2_wellord1(sK2,X1),X0) ),
% 3.33/1.03      inference(superposition,[status(thm)],[c_193,c_195]) ).
% 3.33/1.03  
% 3.33/1.03  cnf(c_7,negated_conjecture,
% 3.33/1.03      ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
% 3.33/1.03      inference(cnf_transformation,[],[f29]) ).
% 3.33/1.03  
% 3.33/1.03  cnf(c_909,plain,
% 3.33/1.03      ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,sK0) ),
% 3.33/1.03      inference(demodulation,[status(thm)],[c_605,c_7]) ).
% 3.33/1.03  
% 3.33/1.03  cnf(contradiction,plain,
% 3.33/1.03      ( $false ),
% 3.33/1.03      inference(minisat,[status(thm)],[c_1905,c_909]) ).
% 3.33/1.03  
% 3.33/1.03  
% 3.33/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.33/1.03  
% 3.33/1.03  ------                               Statistics
% 3.33/1.03  
% 3.33/1.03  ------ Selected
% 3.33/1.03  
% 3.33/1.03  total_time:                             0.131
% 3.33/1.03  
%------------------------------------------------------------------------------
