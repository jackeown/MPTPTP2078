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
% DateTime   : Thu Dec  3 11:44:41 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   55 (  81 expanded)
%              Number of clauses        :   23 (  24 expanded)
%              Number of leaves         :   10 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :   84 ( 144 expanded)
%              Number of equality atoms :   52 (  80 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( k1_relat_1(k7_relat_1(X1,X0)) != X0
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( k1_relat_1(k7_relat_1(sK1,sK0)) != sK0
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) != sK0
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f27,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f19,f24])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X0,X2))) = k1_setfam_1(k2_tarski(X0,k2_xboole_0(X1,X2))) ),
    inference(definition_unfolding,[],[f22,f24,f24,f24])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f21,f24])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f25,f24])).

fof(f26,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f28,plain,(
    k1_relat_1(k7_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_85,plain,
    ( k2_xboole_0(X0,X1) = X1
    | k1_relat_1(sK1) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_8])).

cnf(c_86,plain,
    ( k2_xboole_0(sK0,k1_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_85])).

cnf(c_1,plain,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_4,plain,
    ( k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X0,X2))) = k1_setfam_1(k2_tarski(X0,k2_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_423,plain,
    ( k1_setfam_1(k2_tarski(X0,k2_xboole_0(X0,X1))) = k2_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1,c_4])).

cnf(c_3,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_79,plain,
    ( X0 != X1
    | k2_xboole_0(X2,X1) = X1
    | k1_setfam_1(k2_tarski(X0,X3)) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_3])).

cnf(c_80,plain,
    ( k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_79])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_404,plain,
    ( k2_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_80,c_0])).

cnf(c_1326,plain,
    ( k1_setfam_1(k2_tarski(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_423,c_404])).

cnf(c_1333,plain,
    ( k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) = sK0 ),
    inference(superposition,[status(thm)],[c_86,c_1326])).

cnf(c_5,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k2_tarski(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_9,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_72,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_9])).

cnf(c_73,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_72])).

cnf(c_284,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_5,c_73])).

cnf(c_1702,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_1333,c_284])).

cnf(c_7,negated_conjecture,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1702,c_7])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:08:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.09/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.03  
% 3.09/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.09/1.03  
% 3.09/1.03  ------  iProver source info
% 3.09/1.03  
% 3.09/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.09/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.09/1.03  git: non_committed_changes: false
% 3.09/1.03  git: last_make_outside_of_git: false
% 3.09/1.03  
% 3.09/1.03  ------ 
% 3.09/1.03  ------ Parsing...
% 3.09/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.09/1.03  
% 3.09/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.09/1.03  
% 3.09/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.09/1.03  
% 3.09/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.09/1.03  ------ Proving...
% 3.09/1.03  ------ Problem Properties 
% 3.09/1.03  
% 3.09/1.03  
% 3.09/1.03  clauses                                 8
% 3.09/1.03  conjectures                             1
% 3.09/1.03  EPR                                     0
% 3.09/1.03  Horn                                    8
% 3.09/1.03  unary                                   8
% 3.09/1.03  binary                                  0
% 3.09/1.03  lits                                    8
% 3.09/1.03  lits eq                                 8
% 3.09/1.03  fd_pure                                 0
% 3.09/1.03  fd_pseudo                               0
% 3.09/1.03  fd_cond                                 0
% 3.09/1.03  fd_pseudo_cond                          0
% 3.09/1.03  AC symbols                              0
% 3.09/1.03  
% 3.09/1.03  ------ Input Options Time Limit: Unbounded
% 3.09/1.03  
% 3.09/1.03  
% 3.09/1.03  ------ 
% 3.09/1.03  Current options:
% 3.09/1.03  ------ 
% 3.09/1.03  
% 3.09/1.03  
% 3.09/1.03  
% 3.09/1.03  
% 3.09/1.03  ------ Proving...
% 3.09/1.03  
% 3.09/1.03  
% 3.09/1.03  % SZS status Theorem for theBenchmark.p
% 3.09/1.03  
% 3.09/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.09/1.03  
% 3.09/1.03  fof(f3,axiom,(
% 3.09/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.09/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.03  
% 3.09/1.03  fof(f12,plain,(
% 3.09/1.03    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.09/1.03    inference(ennf_transformation,[],[f3])).
% 3.09/1.03  
% 3.09/1.03  fof(f20,plain,(
% 3.09/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.09/1.03    inference(cnf_transformation,[],[f12])).
% 3.09/1.03  
% 3.09/1.03  fof(f9,conjecture,(
% 3.09/1.03    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.09/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.03  
% 3.09/1.03  fof(f10,negated_conjecture,(
% 3.09/1.03    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.09/1.03    inference(negated_conjecture,[],[f9])).
% 3.09/1.03  
% 3.09/1.03  fof(f14,plain,(
% 3.09/1.03    ? [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 3.09/1.03    inference(ennf_transformation,[],[f10])).
% 3.09/1.03  
% 3.09/1.03  fof(f15,plain,(
% 3.09/1.03    ? [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 3.09/1.03    inference(flattening,[],[f14])).
% 3.09/1.03  
% 3.09/1.03  fof(f16,plain,(
% 3.09/1.03    ? [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (k1_relat_1(k7_relat_1(sK1,sK0)) != sK0 & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 3.09/1.03    introduced(choice_axiom,[])).
% 3.09/1.03  
% 3.09/1.03  fof(f17,plain,(
% 3.09/1.03    k1_relat_1(k7_relat_1(sK1,sK0)) != sK0 & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 3.09/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 3.09/1.03  
% 3.09/1.03  fof(f27,plain,(
% 3.09/1.03    r1_tarski(sK0,k1_relat_1(sK1))),
% 3.09/1.03    inference(cnf_transformation,[],[f17])).
% 3.09/1.03  
% 3.09/1.03  fof(f2,axiom,(
% 3.09/1.03    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.09/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.03  
% 3.09/1.03  fof(f11,plain,(
% 3.09/1.03    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.09/1.03    inference(rectify,[],[f2])).
% 3.09/1.03  
% 3.09/1.03  fof(f19,plain,(
% 3.09/1.03    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.09/1.03    inference(cnf_transformation,[],[f11])).
% 3.09/1.03  
% 3.09/1.03  fof(f7,axiom,(
% 3.09/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.09/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.03  
% 3.09/1.03  fof(f24,plain,(
% 3.09/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.09/1.03    inference(cnf_transformation,[],[f7])).
% 3.09/1.03  
% 3.09/1.03  fof(f29,plain,(
% 3.09/1.03    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 3.09/1.03    inference(definition_unfolding,[],[f19,f24])).
% 3.09/1.03  
% 3.09/1.03  fof(f5,axiom,(
% 3.09/1.03    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.09/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.03  
% 3.09/1.03  fof(f22,plain,(
% 3.09/1.03    ( ! [X2,X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.09/1.03    inference(cnf_transformation,[],[f5])).
% 3.09/1.03  
% 3.09/1.03  fof(f31,plain,(
% 3.09/1.03    ( ! [X2,X0,X1] : (k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X0,X2))) = k1_setfam_1(k2_tarski(X0,k2_xboole_0(X1,X2)))) )),
% 3.09/1.03    inference(definition_unfolding,[],[f22,f24,f24,f24])).
% 3.09/1.03  
% 3.09/1.03  fof(f4,axiom,(
% 3.09/1.03    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.09/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.03  
% 3.09/1.03  fof(f21,plain,(
% 3.09/1.03    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.09/1.03    inference(cnf_transformation,[],[f4])).
% 3.09/1.03  
% 3.09/1.03  fof(f30,plain,(
% 3.09/1.03    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 3.09/1.03    inference(definition_unfolding,[],[f21,f24])).
% 3.09/1.03  
% 3.09/1.03  fof(f1,axiom,(
% 3.09/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.09/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.03  
% 3.09/1.03  fof(f18,plain,(
% 3.09/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.09/1.03    inference(cnf_transformation,[],[f1])).
% 3.09/1.03  
% 3.09/1.03  fof(f6,axiom,(
% 3.09/1.03    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.09/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.03  
% 3.09/1.03  fof(f23,plain,(
% 3.09/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.09/1.03    inference(cnf_transformation,[],[f6])).
% 3.09/1.03  
% 3.09/1.03  fof(f8,axiom,(
% 3.09/1.03    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 3.09/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.09/1.03  
% 3.09/1.03  fof(f13,plain,(
% 3.09/1.03    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.09/1.03    inference(ennf_transformation,[],[f8])).
% 3.09/1.03  
% 3.09/1.03  fof(f25,plain,(
% 3.09/1.03    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.09/1.03    inference(cnf_transformation,[],[f13])).
% 3.09/1.03  
% 3.09/1.03  fof(f32,plain,(
% 3.09/1.03    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.09/1.03    inference(definition_unfolding,[],[f25,f24])).
% 3.09/1.03  
% 3.09/1.03  fof(f26,plain,(
% 3.09/1.03    v1_relat_1(sK1)),
% 3.09/1.03    inference(cnf_transformation,[],[f17])).
% 3.09/1.03  
% 3.09/1.03  fof(f28,plain,(
% 3.09/1.03    k1_relat_1(k7_relat_1(sK1,sK0)) != sK0),
% 3.09/1.03    inference(cnf_transformation,[],[f17])).
% 3.09/1.03  
% 3.09/1.03  cnf(c_2,plain,
% 3.09/1.03      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 3.09/1.03      inference(cnf_transformation,[],[f20]) ).
% 3.09/1.03  
% 3.09/1.03  cnf(c_8,negated_conjecture,
% 3.09/1.03      ( r1_tarski(sK0,k1_relat_1(sK1)) ),
% 3.09/1.03      inference(cnf_transformation,[],[f27]) ).
% 3.09/1.03  
% 3.09/1.03  cnf(c_85,plain,
% 3.09/1.03      ( k2_xboole_0(X0,X1) = X1 | k1_relat_1(sK1) != X1 | sK0 != X0 ),
% 3.09/1.03      inference(resolution_lifted,[status(thm)],[c_2,c_8]) ).
% 3.09/1.03  
% 3.09/1.03  cnf(c_86,plain,
% 3.09/1.03      ( k2_xboole_0(sK0,k1_relat_1(sK1)) = k1_relat_1(sK1) ),
% 3.09/1.03      inference(unflattening,[status(thm)],[c_85]) ).
% 3.09/1.03  
% 3.09/1.03  cnf(c_1,plain,
% 3.09/1.03      ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
% 3.09/1.03      inference(cnf_transformation,[],[f29]) ).
% 3.09/1.03  
% 3.09/1.03  cnf(c_4,plain,
% 3.09/1.03      ( k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X0,X2))) = k1_setfam_1(k2_tarski(X0,k2_xboole_0(X1,X2))) ),
% 3.09/1.03      inference(cnf_transformation,[],[f31]) ).
% 3.09/1.03  
% 3.09/1.03  cnf(c_423,plain,
% 3.09/1.03      ( k1_setfam_1(k2_tarski(X0,k2_xboole_0(X0,X1))) = k2_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
% 3.09/1.03      inference(superposition,[status(thm)],[c_1,c_4]) ).
% 3.09/1.03  
% 3.09/1.03  cnf(c_3,plain,
% 3.09/1.03      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
% 3.09/1.03      inference(cnf_transformation,[],[f30]) ).
% 3.09/1.03  
% 3.09/1.03  cnf(c_79,plain,
% 3.09/1.03      ( X0 != X1
% 3.09/1.03      | k2_xboole_0(X2,X1) = X1
% 3.09/1.03      | k1_setfam_1(k2_tarski(X0,X3)) != X2 ),
% 3.09/1.03      inference(resolution_lifted,[status(thm)],[c_2,c_3]) ).
% 3.09/1.03  
% 3.09/1.03  cnf(c_80,plain,
% 3.09/1.03      ( k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X0) = X0 ),
% 3.09/1.03      inference(unflattening,[status(thm)],[c_79]) ).
% 3.09/1.03  
% 3.09/1.03  cnf(c_0,plain,
% 3.09/1.03      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 3.09/1.03      inference(cnf_transformation,[],[f18]) ).
% 3.09/1.03  
% 3.09/1.03  cnf(c_404,plain,
% 3.09/1.03      ( k2_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X0 ),
% 3.09/1.03      inference(superposition,[status(thm)],[c_80,c_0]) ).
% 3.09/1.03  
% 3.09/1.03  cnf(c_1326,plain,
% 3.09/1.03      ( k1_setfam_1(k2_tarski(X0,k2_xboole_0(X0,X1))) = X0 ),
% 3.09/1.03      inference(light_normalisation,[status(thm)],[c_423,c_404]) ).
% 3.09/1.03  
% 3.09/1.03  cnf(c_1333,plain,
% 3.09/1.03      ( k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) = sK0 ),
% 3.09/1.03      inference(superposition,[status(thm)],[c_86,c_1326]) ).
% 3.09/1.03  
% 3.09/1.03  cnf(c_5,plain,
% 3.09/1.03      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 3.09/1.03      inference(cnf_transformation,[],[f23]) ).
% 3.09/1.03  
% 3.09/1.03  cnf(c_6,plain,
% 3.09/1.03      ( ~ v1_relat_1(X0)
% 3.09/1.03      | k1_setfam_1(k2_tarski(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 3.09/1.03      inference(cnf_transformation,[],[f32]) ).
% 3.09/1.03  
% 3.09/1.03  cnf(c_9,negated_conjecture,
% 3.09/1.03      ( v1_relat_1(sK1) ),
% 3.09/1.03      inference(cnf_transformation,[],[f26]) ).
% 3.09/1.03  
% 3.09/1.03  cnf(c_72,plain,
% 3.09/1.03      ( k1_setfam_1(k2_tarski(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 3.09/1.03      | sK1 != X0 ),
% 3.09/1.03      inference(resolution_lifted,[status(thm)],[c_6,c_9]) ).
% 3.09/1.03  
% 3.09/1.03  cnf(c_73,plain,
% 3.09/1.03      ( k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 3.09/1.03      inference(unflattening,[status(thm)],[c_72]) ).
% 3.09/1.03  
% 3.09/1.03  cnf(c_284,plain,
% 3.09/1.03      ( k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 3.09/1.03      inference(superposition,[status(thm)],[c_5,c_73]) ).
% 3.09/1.03  
% 3.09/1.03  cnf(c_1702,plain,
% 3.09/1.03      ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
% 3.09/1.03      inference(superposition,[status(thm)],[c_1333,c_284]) ).
% 3.09/1.03  
% 3.09/1.03  cnf(c_7,negated_conjecture,
% 3.09/1.03      ( k1_relat_1(k7_relat_1(sK1,sK0)) != sK0 ),
% 3.09/1.03      inference(cnf_transformation,[],[f28]) ).
% 3.09/1.03  
% 3.09/1.03  cnf(contradiction,plain,
% 3.09/1.03      ( $false ),
% 3.09/1.03      inference(minisat,[status(thm)],[c_1702,c_7]) ).
% 3.09/1.03  
% 3.09/1.03  
% 3.09/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.09/1.03  
% 3.09/1.03  ------                               Statistics
% 3.09/1.03  
% 3.09/1.03  ------ Selected
% 3.09/1.03  
% 3.09/1.03  total_time:                             0.101
% 3.09/1.03  
%------------------------------------------------------------------------------
