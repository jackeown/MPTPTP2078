%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:45 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  75 expanded)
%              Number of clauses        :   22 (  33 expanded)
%              Number of leaves         :    8 (  16 expanded)
%              Depth                    :   11
%              Number of atoms          :   69 ( 119 expanded)
%              Number of equality atoms :   30 (  47 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f22,plain,(
    ~ r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_377,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_3])).

cnf(c_7,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_160,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_162,plain,
    ( k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_627,plain,
    ( k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_160,c_162])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_4,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_163,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_381,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_163])).

cnf(c_818,plain,
    ( r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,k2_xboole_0(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_627,c_381])).

cnf(c_1079,plain,
    ( r1_tarski(k10_relat_1(sK2,k3_xboole_0(X0,X1)),k10_relat_1(sK2,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_377,c_818])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_164,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k3_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_161,plain,
    ( r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_738,plain,
    ( r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k10_relat_1(sK2,sK1)) != iProver_top
    | r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k10_relat_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_164,c_161])).

cnf(c_1652,plain,
    ( r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k10_relat_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1079,c_738])).

cnf(c_1078,plain,
    ( r1_tarski(k10_relat_1(sK2,k3_xboole_0(X0,X1)),k10_relat_1(sK2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_818])).

cnf(c_2201,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1652,c_1078])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:47:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.21/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/0.98  
% 3.21/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.21/0.98  
% 3.21/0.98  ------  iProver source info
% 3.21/0.98  
% 3.21/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.21/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.21/0.98  git: non_committed_changes: false
% 3.21/0.98  git: last_make_outside_of_git: false
% 3.21/0.98  
% 3.21/0.98  ------ 
% 3.21/0.98  ------ Parsing...
% 3.21/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.21/0.98  
% 3.21/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.21/0.98  
% 3.21/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.21/0.98  
% 3.21/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.21/0.98  ------ Proving...
% 3.21/0.98  ------ Problem Properties 
% 3.21/0.98  
% 3.21/0.98  
% 3.21/0.98  clauses                                 8
% 3.21/0.98  conjectures                             2
% 3.21/0.98  EPR                                     1
% 3.21/0.98  Horn                                    8
% 3.21/0.98  unary                                   6
% 3.21/0.98  binary                                  1
% 3.21/0.98  lits                                    11
% 3.21/0.98  lits eq                                 4
% 3.21/0.98  fd_pure                                 0
% 3.21/0.98  fd_pseudo                               0
% 3.21/0.98  fd_cond                                 0
% 3.21/0.98  fd_pseudo_cond                          0
% 3.21/0.98  AC symbols                              0
% 3.21/0.98  
% 3.21/0.98  ------ Input Options Time Limit: Unbounded
% 3.21/0.98  
% 3.21/0.98  
% 3.21/0.98  ------ 
% 3.21/0.98  Current options:
% 3.21/0.98  ------ 
% 3.21/0.98  
% 3.21/0.98  
% 3.21/0.98  
% 3.21/0.98  
% 3.21/0.98  ------ Proving...
% 3.21/0.98  
% 3.21/0.98  
% 3.21/0.98  % SZS status Theorem for theBenchmark.p
% 3.21/0.98  
% 3.21/0.98   Resolution empty clause
% 3.21/0.98  
% 3.21/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.21/0.98  
% 3.21/0.98  fof(f2,axiom,(
% 3.21/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.21/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/0.98  
% 3.21/0.98  fof(f16,plain,(
% 3.21/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.21/0.98    inference(cnf_transformation,[],[f2])).
% 3.21/0.98  
% 3.21/0.98  fof(f4,axiom,(
% 3.21/0.98    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 3.21/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/0.98  
% 3.21/0.98  fof(f18,plain,(
% 3.21/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 3.21/0.98    inference(cnf_transformation,[],[f4])).
% 3.21/0.98  
% 3.21/0.98  fof(f7,conjecture,(
% 3.21/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 3.21/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/0.98  
% 3.21/0.98  fof(f8,negated_conjecture,(
% 3.21/0.98    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 3.21/0.98    inference(negated_conjecture,[],[f7])).
% 3.21/0.98  
% 3.21/0.98  fof(f12,plain,(
% 3.21/0.98    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) & v1_relat_1(X2))),
% 3.21/0.98    inference(ennf_transformation,[],[f8])).
% 3.21/0.98  
% 3.21/0.98  fof(f13,plain,(
% 3.21/0.98    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) & v1_relat_1(X2)) => (~r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) & v1_relat_1(sK2))),
% 3.21/0.98    introduced(choice_axiom,[])).
% 3.21/0.98  
% 3.21/0.98  fof(f14,plain,(
% 3.21/0.98    ~r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) & v1_relat_1(sK2)),
% 3.21/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 3.21/0.98  
% 3.21/0.98  fof(f21,plain,(
% 3.21/0.98    v1_relat_1(sK2)),
% 3.21/0.98    inference(cnf_transformation,[],[f14])).
% 3.21/0.98  
% 3.21/0.98  fof(f6,axiom,(
% 3.21/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)))),
% 3.21/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/0.98  
% 3.21/0.98  fof(f11,plain,(
% 3.21/0.98    ! [X0,X1,X2] : (k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 3.21/0.98    inference(ennf_transformation,[],[f6])).
% 3.21/0.98  
% 3.21/0.98  fof(f20,plain,(
% 3.21/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 3.21/0.98    inference(cnf_transformation,[],[f11])).
% 3.21/0.98  
% 3.21/0.98  fof(f1,axiom,(
% 3.21/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.21/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/0.98  
% 3.21/0.98  fof(f15,plain,(
% 3.21/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.21/0.98    inference(cnf_transformation,[],[f1])).
% 3.21/0.98  
% 3.21/0.98  fof(f5,axiom,(
% 3.21/0.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.21/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/0.98  
% 3.21/0.98  fof(f19,plain,(
% 3.21/0.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.21/0.98    inference(cnf_transformation,[],[f5])).
% 3.21/0.98  
% 3.21/0.98  fof(f3,axiom,(
% 3.21/0.98    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.21/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/0.98  
% 3.21/0.98  fof(f9,plain,(
% 3.21/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.21/0.98    inference(ennf_transformation,[],[f3])).
% 3.21/0.98  
% 3.21/0.98  fof(f10,plain,(
% 3.21/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.21/0.98    inference(flattening,[],[f9])).
% 3.21/0.98  
% 3.21/0.98  fof(f17,plain,(
% 3.21/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.21/0.98    inference(cnf_transformation,[],[f10])).
% 3.21/0.98  
% 3.21/0.98  fof(f22,plain,(
% 3.21/0.98    ~r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),
% 3.21/0.98    inference(cnf_transformation,[],[f14])).
% 3.21/0.98  
% 3.21/0.98  cnf(c_1,plain,
% 3.21/0.98      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.21/0.98      inference(cnf_transformation,[],[f16]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_3,plain,
% 3.21/0.98      ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 3.21/0.98      inference(cnf_transformation,[],[f18]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_377,plain,
% 3.21/0.98      ( k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
% 3.21/0.98      inference(superposition,[status(thm)],[c_1,c_3]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_7,negated_conjecture,
% 3.21/0.98      ( v1_relat_1(sK2) ),
% 3.21/0.98      inference(cnf_transformation,[],[f21]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_160,plain,
% 3.21/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 3.21/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_5,plain,
% 3.21/0.98      ( ~ v1_relat_1(X0)
% 3.21/0.98      | k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2)) ),
% 3.21/0.98      inference(cnf_transformation,[],[f20]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_162,plain,
% 3.21/0.98      ( k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2))
% 3.21/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.21/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_627,plain,
% 3.21/0.98      ( k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k2_xboole_0(X0,X1)) ),
% 3.21/0.98      inference(superposition,[status(thm)],[c_160,c_162]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_0,plain,
% 3.21/0.98      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 3.21/0.98      inference(cnf_transformation,[],[f15]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_4,plain,
% 3.21/0.98      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 3.21/0.98      inference(cnf_transformation,[],[f19]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_163,plain,
% 3.21/0.98      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 3.21/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_381,plain,
% 3.21/0.98      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 3.21/0.98      inference(superposition,[status(thm)],[c_0,c_163]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_818,plain,
% 3.21/0.98      ( r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,k2_xboole_0(X1,X0))) = iProver_top ),
% 3.21/0.98      inference(superposition,[status(thm)],[c_627,c_381]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_1079,plain,
% 3.21/0.98      ( r1_tarski(k10_relat_1(sK2,k3_xboole_0(X0,X1)),k10_relat_1(sK2,X1)) = iProver_top ),
% 3.21/0.98      inference(superposition,[status(thm)],[c_377,c_818]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_2,plain,
% 3.21/0.98      ( ~ r1_tarski(X0,X1)
% 3.21/0.98      | ~ r1_tarski(X0,X2)
% 3.21/0.98      | r1_tarski(X0,k3_xboole_0(X2,X1)) ),
% 3.21/0.98      inference(cnf_transformation,[],[f17]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_164,plain,
% 3.21/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.21/0.98      | r1_tarski(X0,X2) != iProver_top
% 3.21/0.98      | r1_tarski(X0,k3_xboole_0(X2,X1)) = iProver_top ),
% 3.21/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_6,negated_conjecture,
% 3.21/0.98      ( ~ r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) ),
% 3.21/0.98      inference(cnf_transformation,[],[f22]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_161,plain,
% 3.21/0.98      ( r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) != iProver_top ),
% 3.21/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_738,plain,
% 3.21/0.98      ( r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k10_relat_1(sK2,sK1)) != iProver_top
% 3.21/0.98      | r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k10_relat_1(sK2,sK0)) != iProver_top ),
% 3.21/0.98      inference(superposition,[status(thm)],[c_164,c_161]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_1652,plain,
% 3.21/0.98      ( r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k10_relat_1(sK2,sK0)) != iProver_top ),
% 3.21/0.98      inference(superposition,[status(thm)],[c_1079,c_738]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_1078,plain,
% 3.21/0.98      ( r1_tarski(k10_relat_1(sK2,k3_xboole_0(X0,X1)),k10_relat_1(sK2,X0)) = iProver_top ),
% 3.21/0.98      inference(superposition,[status(thm)],[c_3,c_818]) ).
% 3.21/0.98  
% 3.21/0.98  cnf(c_2201,plain,
% 3.21/0.98      ( $false ),
% 3.21/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_1652,c_1078]) ).
% 3.21/0.98  
% 3.21/0.98  
% 3.21/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.21/0.98  
% 3.21/0.98  ------                               Statistics
% 3.21/0.98  
% 3.21/0.98  ------ Selected
% 3.21/0.98  
% 3.21/0.98  total_time:                             0.085
% 3.21/0.98  
%------------------------------------------------------------------------------
