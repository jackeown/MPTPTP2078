%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:58 EST 2020

% Result     : Theorem 11.41s
% Output     : CNFRefutation 11.41s
% Verified   : 
% Statistics : Number of formulae       :   55 (  98 expanded)
%              Number of clauses        :   14 (  18 expanded)
%              Number of leaves         :   14 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :   70 ( 113 expanded)
%              Number of equality atoms :   58 ( 101 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f12,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f37,f31])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f35,f43])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != o_0_0_xboole_0 ) ),
    inference(definition_unfolding,[],[f30,f28,f31])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f43])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f36,f28])).

fof(f17,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f17])).

fof(f23,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f18])).

fof(f24,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)
   => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f24])).

fof(f42,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f38,f43,f40])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k2_tarski(X0,X0)))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f39,f43,f40,f44])).

fof(f51,plain,(
    k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k2_tarski(sK0,sK0)))) ),
    inference(definition_unfolding,[],[f42,f44,f45])).

cnf(c_8,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_7,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_64,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_8,c_7,c_1])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_47,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != o_0_0_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_6])).

cnf(c_62,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = X1
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != o_0_0_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_47,c_7,c_1])).

cnf(c_370,plain,
    ( k5_xboole_0(X0,X0) != o_0_0_xboole_0
    | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_64,c_62])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_34286,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_370,c_9])).

cnf(c_10,negated_conjecture,
    ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k2_tarski(sK0,sK0)))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_63,negated_conjecture,
    ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))),k3_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2))))))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))) ),
    inference(theory_normalisation,[status(thm)],[c_10,c_7,c_1])).

cnf(c_34551,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_34286,c_63])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 21:01:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 11.41/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.41/1.99  
% 11.41/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.41/1.99  
% 11.41/1.99  ------  iProver source info
% 11.41/1.99  
% 11.41/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.41/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.41/1.99  git: non_committed_changes: false
% 11.41/1.99  git: last_make_outside_of_git: false
% 11.41/1.99  
% 11.41/1.99  ------ 
% 11.41/1.99  ------ Parsing...
% 11.41/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.41/1.99  
% 11.41/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.41/1.99  
% 11.41/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.41/1.99  
% 11.41/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.41/1.99  ------ Proving...
% 11.41/1.99  ------ Problem Properties 
% 11.41/1.99  
% 11.41/1.99  
% 11.41/1.99  clauses                                 10
% 11.41/1.99  conjectures                             1
% 11.41/1.99  EPR                                     0
% 11.41/1.99  Horn                                    10
% 11.41/1.99  unary                                   9
% 11.41/1.99  binary                                  1
% 11.41/1.99  lits                                    11
% 11.41/1.99  lits eq                                 11
% 11.41/1.99  fd_pure                                 0
% 11.41/1.99  fd_pseudo                               0
% 11.41/1.99  fd_cond                                 0
% 11.41/1.99  fd_pseudo_cond                          0
% 11.41/1.99  AC symbols                              1
% 11.41/1.99  
% 11.41/1.99  ------ Input Options Time Limit: Unbounded
% 11.41/1.99  
% 11.41/1.99  
% 11.41/1.99  ------ 
% 11.41/1.99  Current options:
% 11.41/1.99  ------ 
% 11.41/1.99  
% 11.41/1.99  
% 11.41/1.99  
% 11.41/1.99  
% 11.41/1.99  ------ Proving...
% 11.41/1.99  
% 11.41/1.99  
% 11.41/1.99  % SZS status Theorem for theBenchmark.p
% 11.41/1.99  
% 11.41/1.99   Resolution empty clause
% 11.41/1.99  
% 11.41/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.41/1.99  
% 11.41/1.99  fof(f10,axiom,(
% 11.41/1.99    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 11.41/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f35,plain,(
% 11.41/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 11.41/1.99    inference(cnf_transformation,[],[f10])).
% 11.41/1.99  
% 11.41/1.99  fof(f12,axiom,(
% 11.41/1.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 11.41/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f37,plain,(
% 11.41/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f12])).
% 11.41/1.99  
% 11.41/1.99  fof(f6,axiom,(
% 11.41/1.99    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 11.41/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f31,plain,(
% 11.41/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f6])).
% 11.41/1.99  
% 11.41/1.99  fof(f43,plain,(
% 11.41/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 11.41/1.99    inference(definition_unfolding,[],[f37,f31])).
% 11.41/1.99  
% 11.41/1.99  fof(f49,plain,(
% 11.41/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 11.41/1.99    inference(definition_unfolding,[],[f35,f43])).
% 11.41/1.99  
% 11.41/1.99  fof(f9,axiom,(
% 11.41/1.99    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 11.41/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f34,plain,(
% 11.41/1.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f9])).
% 11.41/1.99  
% 11.41/1.99  fof(f1,axiom,(
% 11.41/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.41/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f26,plain,(
% 11.41/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f1])).
% 11.41/1.99  
% 11.41/1.99  fof(f5,axiom,(
% 11.41/1.99    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 11.41/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f20,plain,(
% 11.41/1.99    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) => r1_tarski(X0,X1))),
% 11.41/1.99    inference(unused_predicate_definition_removal,[],[f5])).
% 11.41/1.99  
% 11.41/1.99  fof(f21,plain,(
% 11.41/1.99    ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1))),
% 11.41/1.99    inference(ennf_transformation,[],[f20])).
% 11.41/1.99  
% 11.41/1.99  fof(f30,plain,(
% 11.41/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f21])).
% 11.41/1.99  
% 11.41/1.99  fof(f3,axiom,(
% 11.41/1.99    k1_xboole_0 = o_0_0_xboole_0),
% 11.41/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f28,plain,(
% 11.41/1.99    k1_xboole_0 = o_0_0_xboole_0),
% 11.41/1.99    inference(cnf_transformation,[],[f3])).
% 11.41/1.99  
% 11.41/1.99  fof(f47,plain,(
% 11.41/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != o_0_0_xboole_0) )),
% 11.41/1.99    inference(definition_unfolding,[],[f30,f28,f31])).
% 11.41/1.99  
% 11.41/1.99  fof(f8,axiom,(
% 11.41/1.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.41/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f22,plain,(
% 11.41/1.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.41/1.99    inference(ennf_transformation,[],[f8])).
% 11.41/1.99  
% 11.41/1.99  fof(f33,plain,(
% 11.41/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f22])).
% 11.41/1.99  
% 11.41/1.99  fof(f48,plain,(
% 11.41/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 | ~r1_tarski(X0,X1)) )),
% 11.41/1.99    inference(definition_unfolding,[],[f33,f43])).
% 11.41/1.99  
% 11.41/1.99  fof(f11,axiom,(
% 11.41/1.99    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 11.41/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f36,plain,(
% 11.41/1.99    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 11.41/1.99    inference(cnf_transformation,[],[f11])).
% 11.41/1.99  
% 11.41/1.99  fof(f50,plain,(
% 11.41/1.99    ( ! [X0] : (k5_xboole_0(X0,X0) = o_0_0_xboole_0) )),
% 11.41/1.99    inference(definition_unfolding,[],[f36,f28])).
% 11.41/1.99  
% 11.41/1.99  fof(f17,conjecture,(
% 11.41/1.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.41/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f18,negated_conjecture,(
% 11.41/1.99    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.41/1.99    inference(negated_conjecture,[],[f17])).
% 11.41/1.99  
% 11.41/1.99  fof(f23,plain,(
% 11.41/1.99    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)),
% 11.41/1.99    inference(ennf_transformation,[],[f18])).
% 11.41/1.99  
% 11.41/1.99  fof(f24,plain,(
% 11.41/1.99    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 11.41/1.99    introduced(choice_axiom,[])).
% 11.41/1.99  
% 11.41/1.99  fof(f25,plain,(
% 11.41/1.99    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 11.41/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f24])).
% 11.41/1.99  
% 11.41/1.99  fof(f42,plain,(
% 11.41/1.99    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 11.41/1.99    inference(cnf_transformation,[],[f25])).
% 11.41/1.99  
% 11.41/1.99  fof(f14,axiom,(
% 11.41/1.99    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 11.41/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f39,plain,(
% 11.41/1.99    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f14])).
% 11.41/1.99  
% 11.41/1.99  fof(f13,axiom,(
% 11.41/1.99    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)),
% 11.41/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f38,plain,(
% 11.41/1.99    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f13])).
% 11.41/1.99  
% 11.41/1.99  fof(f15,axiom,(
% 11.41/1.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 11.41/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.41/1.99  
% 11.41/1.99  fof(f40,plain,(
% 11.41/1.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 11.41/1.99    inference(cnf_transformation,[],[f15])).
% 11.41/1.99  
% 11.41/1.99  fof(f44,plain,(
% 11.41/1.99    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k1_enumset1(X0,X1,X2)) )),
% 11.41/1.99    inference(definition_unfolding,[],[f38,f43,f40])).
% 11.41/1.99  
% 11.41/1.99  fof(f45,plain,(
% 11.41/1.99    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k2_tarski(X0,X0)))) = k2_enumset1(X0,X1,X2,X3)) )),
% 11.41/1.99    inference(definition_unfolding,[],[f39,f43,f40,f44])).
% 11.41/1.99  
% 11.41/1.99  fof(f51,plain,(
% 11.41/1.99    k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k2_tarski(sK0,sK0))))),
% 11.41/1.99    inference(definition_unfolding,[],[f42,f44,f45])).
% 11.41/1.99  
% 11.41/1.99  cnf(c_8,plain,
% 11.41/1.99      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 11.41/1.99      inference(cnf_transformation,[],[f49]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_7,plain,
% 11.41/1.99      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 11.41/1.99      inference(cnf_transformation,[],[f34]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1,plain,
% 11.41/1.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 11.41/1.99      inference(cnf_transformation,[],[f26]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_64,plain,
% 11.41/1.99      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
% 11.41/1.99      inference(theory_normalisation,[status(thm)],[c_8,c_7,c_1]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_4,plain,
% 11.41/1.99      ( r1_tarski(X0,X1)
% 11.41/1.99      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != o_0_0_xboole_0 ),
% 11.41/1.99      inference(cnf_transformation,[],[f47]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_6,plain,
% 11.41/1.99      ( ~ r1_tarski(X0,X1)
% 11.41/1.99      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 ),
% 11.41/1.99      inference(cnf_transformation,[],[f48]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_47,plain,
% 11.41/1.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1
% 11.41/1.99      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != o_0_0_xboole_0 ),
% 11.41/1.99      inference(resolution,[status(thm)],[c_4,c_6]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_62,plain,
% 11.41/1.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = X1
% 11.41/1.99      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != o_0_0_xboole_0 ),
% 11.41/1.99      inference(theory_normalisation,[status(thm)],[c_47,c_7,c_1]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_370,plain,
% 11.41/1.99      ( k5_xboole_0(X0,X0) != o_0_0_xboole_0
% 11.41/1.99      | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_64,c_62]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_9,plain,
% 11.41/1.99      ( k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
% 11.41/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_34286,plain,
% 11.41/1.99      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
% 11.41/1.99      inference(global_propositional_subsumption,[status(thm)],[c_370,c_9]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_10,negated_conjecture,
% 11.41/1.99      ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k2_tarski(sK0,sK0)))) ),
% 11.41/1.99      inference(cnf_transformation,[],[f51]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_63,negated_conjecture,
% 11.41/1.99      ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))),k3_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2))))))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))) ),
% 11.41/1.99      inference(theory_normalisation,[status(thm)],[c_10,c_7,c_1]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_34551,plain,
% 11.41/1.99      ( $false ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_34286,c_63]) ).
% 11.41/1.99  
% 11.41/1.99  
% 11.41/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.41/1.99  
% 11.41/1.99  ------                               Statistics
% 11.41/1.99  
% 11.41/1.99  ------ Selected
% 11.41/1.99  
% 11.41/1.99  total_time:                             1.217
% 11.41/1.99  
%------------------------------------------------------------------------------
