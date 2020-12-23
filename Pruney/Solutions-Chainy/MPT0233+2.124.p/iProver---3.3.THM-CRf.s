%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:31:30 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 140 expanded)
%              Number of clauses        :   29 (  37 expanded)
%              Number of leaves         :   13 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :  121 ( 245 expanded)
%              Number of equality atoms :   68 ( 167 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK0 != sK3
      & sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( sK0 != sK3
    & sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f15])).

fof(f25,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f32,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f25,f28,f28])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f20,f28])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | X0 = X1
      | ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f24,f29,f28])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f23,f29,f28])).

fof(f27,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f16])).

fof(f26,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_67,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_65,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_709,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_67,c_65])).

cnf(c_66,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_439,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_66,c_65])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_445,plain,
    ( ~ r1_tarski(X0,X1)
    | X0 = k3_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_439,c_2])).

cnf(c_910,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,X2)
    | ~ r1_tarski(k3_xboole_0(X0,X1),X2) ),
    inference(resolution,[status(thm)],[c_709,c_445])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_903,plain,
    ( ~ r1_tarski(k3_xboole_0(X0,X1),X2)
    | r1_tarski(k3_xboole_0(X1,X0),X2) ),
    inference(resolution,[status(thm)],[c_709,c_0])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_1040,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_xboole_0(X2,X0),X1) ),
    inference(resolution,[status(thm)],[c_903,c_1])).

cnf(c_1212,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(resolution,[status(thm)],[c_910,c_1040])).

cnf(c_7,negated_conjecture,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1226,plain,
    ( r1_tarski(X0,k2_enumset1(sK2,sK2,sK2,sK3))
    | ~ r1_tarski(X0,k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(resolution,[status(thm)],[c_1212,c_7])).

cnf(c_4,plain,
    ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2))
    | X1 = X0
    | X2 = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1298,plain,
    ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(sK0,sK0,sK0,sK1))
    | sK2 = X0
    | sK3 = X0 ),
    inference(resolution,[status(thm)],[c_1226,c_4])).

cnf(c_1300,plain,
    ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1))
    | sK2 = sK0
    | sK3 = sK0 ),
    inference(instantiation,[status(thm)],[c_1298])).

cnf(c_3,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_475,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_224,plain,
    ( sK2 != X0
    | sK0 != X0
    | sK0 = sK2 ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_225,plain,
    ( sK2 != sK0
    | sK0 = sK2
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_224])).

cnf(c_222,plain,
    ( sK3 != X0
    | sK0 != X0
    | sK0 = sK3 ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_223,plain,
    ( sK3 != sK0
    | sK0 = sK3
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_222])).

cnf(c_13,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_10,plain,
    ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5,negated_conjecture,
    ( sK0 != sK3 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_6,negated_conjecture,
    ( sK0 != sK2 ),
    inference(cnf_transformation,[],[f26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1300,c_475,c_225,c_223,c_13,c_10,c_5,c_6])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:21:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.41/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/0.98  
% 2.41/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.41/0.98  
% 2.41/0.98  ------  iProver source info
% 2.41/0.98  
% 2.41/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.41/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.41/0.98  git: non_committed_changes: false
% 2.41/0.98  git: last_make_outside_of_git: false
% 2.41/0.98  
% 2.41/0.98  ------ 
% 2.41/0.98  ------ Parsing...
% 2.41/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.41/0.98  
% 2.41/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.41/0.98  
% 2.41/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.41/0.98  
% 2.41/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.41/0.98  ------ Proving...
% 2.41/0.98  ------ Problem Properties 
% 2.41/0.98  
% 2.41/0.98  
% 2.41/0.98  clauses                                 8
% 2.41/0.98  conjectures                             3
% 2.41/0.98  EPR                                     2
% 2.41/0.98  Horn                                    7
% 2.41/0.98  unary                                   5
% 2.41/0.98  binary                                  2
% 2.41/0.98  lits                                    12
% 2.41/0.98  lits eq                                 6
% 2.41/0.98  fd_pure                                 0
% 2.41/0.98  fd_pseudo                               0
% 2.41/0.98  fd_cond                                 0
% 2.41/0.98  fd_pseudo_cond                          1
% 2.41/0.98  AC symbols                              0
% 2.41/0.98  
% 2.41/0.98  ------ Input Options Time Limit: Unbounded
% 2.41/0.98  
% 2.41/0.98  
% 2.41/0.98  ------ 
% 2.41/0.98  Current options:
% 2.41/0.98  ------ 
% 2.41/0.98  
% 2.41/0.98  
% 2.41/0.98  
% 2.41/0.98  
% 2.41/0.98  ------ Proving...
% 2.41/0.98  
% 2.41/0.98  
% 2.41/0.98  % SZS status Theorem for theBenchmark.p
% 2.41/0.98  
% 2.41/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.41/0.98  
% 2.41/0.98  fof(f3,axiom,(
% 2.41/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.41/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.98  
% 2.41/0.98  fof(f12,plain,(
% 2.41/0.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.41/0.98    inference(ennf_transformation,[],[f3])).
% 2.41/0.98  
% 2.41/0.98  fof(f19,plain,(
% 2.41/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.41/0.98    inference(cnf_transformation,[],[f12])).
% 2.41/0.98  
% 2.41/0.98  fof(f1,axiom,(
% 2.41/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.41/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.98  
% 2.41/0.98  fof(f17,plain,(
% 2.41/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.41/0.98    inference(cnf_transformation,[],[f1])).
% 2.41/0.98  
% 2.41/0.98  fof(f2,axiom,(
% 2.41/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 2.41/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.98  
% 2.41/0.98  fof(f11,plain,(
% 2.41/0.98    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 2.41/0.98    inference(ennf_transformation,[],[f2])).
% 2.41/0.98  
% 2.41/0.98  fof(f18,plain,(
% 2.41/0.98    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 2.41/0.98    inference(cnf_transformation,[],[f11])).
% 2.41/0.98  
% 2.41/0.98  fof(f9,conjecture,(
% 2.41/0.98    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 2.41/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.98  
% 2.41/0.98  fof(f10,negated_conjecture,(
% 2.41/0.98    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 2.41/0.98    inference(negated_conjecture,[],[f9])).
% 2.41/0.98  
% 2.41/0.98  fof(f14,plain,(
% 2.41/0.98    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 2.41/0.98    inference(ennf_transformation,[],[f10])).
% 2.41/0.98  
% 2.41/0.98  fof(f15,plain,(
% 2.41/0.98    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)))),
% 2.41/0.98    introduced(choice_axiom,[])).
% 2.41/0.98  
% 2.41/0.98  fof(f16,plain,(
% 2.41/0.98    sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 2.41/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f15])).
% 2.41/0.98  
% 2.41/0.98  fof(f25,plain,(
% 2.41/0.98    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 2.41/0.98    inference(cnf_transformation,[],[f16])).
% 2.41/0.98  
% 2.41/0.98  fof(f5,axiom,(
% 2.41/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.41/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.98  
% 2.41/0.98  fof(f21,plain,(
% 2.41/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.41/0.98    inference(cnf_transformation,[],[f5])).
% 2.41/0.98  
% 2.41/0.98  fof(f6,axiom,(
% 2.41/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.41/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.98  
% 2.41/0.98  fof(f22,plain,(
% 2.41/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.41/0.98    inference(cnf_transformation,[],[f6])).
% 2.41/0.98  
% 2.41/0.98  fof(f28,plain,(
% 2.41/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.41/0.98    inference(definition_unfolding,[],[f21,f22])).
% 2.41/0.98  
% 2.41/0.98  fof(f32,plain,(
% 2.41/0.98    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3))),
% 2.41/0.98    inference(definition_unfolding,[],[f25,f28,f28])).
% 2.41/0.98  
% 2.41/0.98  fof(f8,axiom,(
% 2.41/0.98    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 2.41/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.98  
% 2.41/0.98  fof(f13,plain,(
% 2.41/0.98    ! [X0,X1,X2] : (X0 = X2 | X0 = X1 | ~r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 2.41/0.98    inference(ennf_transformation,[],[f8])).
% 2.41/0.98  
% 2.41/0.98  fof(f24,plain,(
% 2.41/0.98    ( ! [X2,X0,X1] : (X0 = X2 | X0 = X1 | ~r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 2.41/0.98    inference(cnf_transformation,[],[f13])).
% 2.41/0.98  
% 2.41/0.98  fof(f4,axiom,(
% 2.41/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.41/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.98  
% 2.41/0.98  fof(f20,plain,(
% 2.41/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.41/0.98    inference(cnf_transformation,[],[f4])).
% 2.41/0.98  
% 2.41/0.98  fof(f29,plain,(
% 2.41/0.98    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.41/0.98    inference(definition_unfolding,[],[f20,f28])).
% 2.41/0.98  
% 2.41/0.98  fof(f31,plain,(
% 2.41/0.98    ( ! [X2,X0,X1] : (X0 = X2 | X0 = X1 | ~r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2))) )),
% 2.41/0.98    inference(definition_unfolding,[],[f24,f29,f28])).
% 2.41/0.98  
% 2.41/0.98  fof(f7,axiom,(
% 2.41/0.98    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 2.41/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.98  
% 2.41/0.98  fof(f23,plain,(
% 2.41/0.98    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 2.41/0.98    inference(cnf_transformation,[],[f7])).
% 2.41/0.98  
% 2.41/0.98  fof(f30,plain,(
% 2.41/0.98    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1))) )),
% 2.41/0.98    inference(definition_unfolding,[],[f23,f29,f28])).
% 2.41/0.98  
% 2.41/0.98  fof(f27,plain,(
% 2.41/0.98    sK0 != sK3),
% 2.41/0.98    inference(cnf_transformation,[],[f16])).
% 2.41/0.98  
% 2.41/0.98  fof(f26,plain,(
% 2.41/0.98    sK0 != sK2),
% 2.41/0.98    inference(cnf_transformation,[],[f16])).
% 2.41/0.98  
% 2.41/0.98  cnf(c_67,plain,
% 2.41/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.41/0.98      theory(equality) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_65,plain,( X0 = X0 ),theory(equality) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_709,plain,
% 2.41/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 2.41/0.98      inference(resolution,[status(thm)],[c_67,c_65]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_66,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_439,plain,
% 2.41/0.98      ( X0 != X1 | X1 = X0 ),
% 2.41/0.98      inference(resolution,[status(thm)],[c_66,c_65]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_2,plain,
% 2.41/0.98      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 2.41/0.98      inference(cnf_transformation,[],[f19]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_445,plain,
% 2.41/0.98      ( ~ r1_tarski(X0,X1) | X0 = k3_xboole_0(X0,X1) ),
% 2.41/0.98      inference(resolution,[status(thm)],[c_439,c_2]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_910,plain,
% 2.41/0.98      ( ~ r1_tarski(X0,X1)
% 2.41/0.98      | r1_tarski(X0,X2)
% 2.41/0.98      | ~ r1_tarski(k3_xboole_0(X0,X1),X2) ),
% 2.41/0.98      inference(resolution,[status(thm)],[c_709,c_445]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_0,plain,
% 2.41/0.98      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 2.41/0.98      inference(cnf_transformation,[],[f17]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_903,plain,
% 2.41/0.98      ( ~ r1_tarski(k3_xboole_0(X0,X1),X2)
% 2.41/0.98      | r1_tarski(k3_xboole_0(X1,X0),X2) ),
% 2.41/0.98      inference(resolution,[status(thm)],[c_709,c_0]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1,plain,
% 2.41/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(k3_xboole_0(X0,X2),X1) ),
% 2.41/0.98      inference(cnf_transformation,[],[f18]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1040,plain,
% 2.41/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(k3_xboole_0(X2,X0),X1) ),
% 2.41/0.98      inference(resolution,[status(thm)],[c_903,c_1]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1212,plain,
% 2.41/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 2.41/0.98      inference(resolution,[status(thm)],[c_910,c_1040]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_7,negated_conjecture,
% 2.41/0.98      ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3)) ),
% 2.41/0.98      inference(cnf_transformation,[],[f32]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1226,plain,
% 2.41/0.98      ( r1_tarski(X0,k2_enumset1(sK2,sK2,sK2,sK3))
% 2.41/0.98      | ~ r1_tarski(X0,k2_enumset1(sK0,sK0,sK0,sK1)) ),
% 2.41/0.98      inference(resolution,[status(thm)],[c_1212,c_7]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_4,plain,
% 2.41/0.98      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2))
% 2.41/0.98      | X1 = X0
% 2.41/0.98      | X2 = X0 ),
% 2.41/0.98      inference(cnf_transformation,[],[f31]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1298,plain,
% 2.41/0.98      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(sK0,sK0,sK0,sK1))
% 2.41/0.98      | sK2 = X0
% 2.41/0.98      | sK3 = X0 ),
% 2.41/0.98      inference(resolution,[status(thm)],[c_1226,c_4]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_1300,plain,
% 2.41/0.98      ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1))
% 2.41/0.98      | sK2 = sK0
% 2.41/0.98      | sK3 = sK0 ),
% 2.41/0.98      inference(instantiation,[status(thm)],[c_1298]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_3,plain,
% 2.41/0.98      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) ),
% 2.41/0.98      inference(cnf_transformation,[],[f30]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_475,plain,
% 2.41/0.98      ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1)) ),
% 2.41/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_224,plain,
% 2.41/0.98      ( sK2 != X0 | sK0 != X0 | sK0 = sK2 ),
% 2.41/0.98      inference(instantiation,[status(thm)],[c_66]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_225,plain,
% 2.41/0.98      ( sK2 != sK0 | sK0 = sK2 | sK0 != sK0 ),
% 2.41/0.98      inference(instantiation,[status(thm)],[c_224]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_222,plain,
% 2.41/0.98      ( sK3 != X0 | sK0 != X0 | sK0 = sK3 ),
% 2.41/0.98      inference(instantiation,[status(thm)],[c_66]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_223,plain,
% 2.41/0.98      ( sK3 != sK0 | sK0 = sK3 | sK0 != sK0 ),
% 2.41/0.98      inference(instantiation,[status(thm)],[c_222]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_13,plain,
% 2.41/0.98      ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 2.41/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_10,plain,
% 2.41/0.98      ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))
% 2.41/0.98      | sK0 = sK0 ),
% 2.41/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_5,negated_conjecture,
% 2.41/0.98      ( sK0 != sK3 ),
% 2.41/0.98      inference(cnf_transformation,[],[f27]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(c_6,negated_conjecture,
% 2.41/0.98      ( sK0 != sK2 ),
% 2.41/0.98      inference(cnf_transformation,[],[f26]) ).
% 2.41/0.98  
% 2.41/0.98  cnf(contradiction,plain,
% 2.41/0.98      ( $false ),
% 2.41/0.98      inference(minisat,
% 2.41/0.98                [status(thm)],
% 2.41/0.98                [c_1300,c_475,c_225,c_223,c_13,c_10,c_5,c_6]) ).
% 2.41/0.98  
% 2.41/0.98  
% 2.41/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.41/0.98  
% 2.41/0.98  ------                               Statistics
% 2.41/0.98  
% 2.41/0.98  ------ Selected
% 2.41/0.98  
% 2.41/0.98  total_time:                             0.081
% 2.41/0.98  
%------------------------------------------------------------------------------
