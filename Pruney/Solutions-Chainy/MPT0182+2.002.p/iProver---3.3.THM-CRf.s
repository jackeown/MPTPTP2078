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
% DateTime   : Thu Dec  3 11:27:40 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :   38 (  89 expanded)
%              Number of clauses        :    9 (  11 expanded)
%              Number of leaves         :   10 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :   39 (  90 expanded)
%              Number of equality atoms :   38 (  89 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f36])).

fof(f43,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f22,f37,f37])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f21,f20])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f27,f37])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3)))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f25,f35,f30,f39])).

fof(f15,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(negated_conjecture,[],[f15])).

fof(f17,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2) ),
    inference(ennf_transformation,[],[f16])).

fof(f18,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2)
   => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).

fof(f34,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    k3_enumset1(sK0,sK0,sK0,sK1,sK2) != k3_enumset1(sK1,sK1,sK1,sK0,sK2) ),
    inference(definition_unfolding,[],[f34,f36,f36])).

cnf(c_1,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_18,plain,
    ( k3_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35) = k3_enumset1(X1_35,X1_35,X1_35,X1_35,X0_35) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2,plain,
    ( k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3)))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_17,plain,
    ( k5_xboole_0(k3_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35),k5_xboole_0(k3_enumset1(X4_35,X4_35,X4_35,X4_35,X4_35),k3_xboole_0(k3_enumset1(X4_35,X4_35,X4_35,X4_35,X4_35),k3_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35)))) = k3_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_86,plain,
    ( k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35),k5_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X2_35,X2_35),k3_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X2_35,X2_35),k3_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35)))) = k3_enumset1(X1_35,X1_35,X1_35,X0_35,X2_35) ),
    inference(superposition,[status(thm)],[c_18,c_17])).

cnf(c_1094,plain,
    ( k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35) = k3_enumset1(X1_35,X1_35,X1_35,X0_35,X2_35) ),
    inference(superposition,[status(thm)],[c_86,c_17])).

cnf(c_5,negated_conjecture,
    ( k3_enumset1(sK0,sK0,sK0,sK1,sK2) != k3_enumset1(sK1,sK1,sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_14,negated_conjecture,
    ( k3_enumset1(sK0,sK0,sK0,sK1,sK2) != k3_enumset1(sK1,sK1,sK1,sK0,sK2) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1590,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1094,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:26:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.55/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/0.99  
% 3.55/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.55/0.99  
% 3.55/0.99  ------  iProver source info
% 3.55/0.99  
% 3.55/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.55/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.55/0.99  git: non_committed_changes: false
% 3.55/0.99  git: last_make_outside_of_git: false
% 3.55/0.99  
% 3.55/0.99  ------ 
% 3.55/0.99  ------ Parsing...
% 3.55/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.55/0.99  
% 3.55/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 3.55/0.99  
% 3.55/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.55/0.99  
% 3.55/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.55/0.99  ------ Proving...
% 3.55/0.99  ------ Problem Properties 
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  clauses                                 6
% 3.55/0.99  conjectures                             1
% 3.55/0.99  EPR                                     0
% 3.55/0.99  Horn                                    6
% 3.55/0.99  unary                                   6
% 3.55/0.99  binary                                  0
% 3.55/0.99  lits                                    6
% 3.55/0.99  lits eq                                 6
% 3.55/0.99  fd_pure                                 0
% 3.55/0.99  fd_pseudo                               0
% 3.55/0.99  fd_cond                                 0
% 3.55/0.99  fd_pseudo_cond                          0
% 3.55/0.99  AC symbols                              0
% 3.55/0.99  
% 3.55/0.99  ------ Input Options Time Limit: Unbounded
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  ------ 
% 3.55/0.99  Current options:
% 3.55/0.99  ------ 
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  ------ Proving...
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  % SZS status Theorem for theBenchmark.p
% 3.55/0.99  
% 3.55/0.99   Resolution empty clause
% 3.55/0.99  
% 3.55/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.55/0.99  
% 3.55/0.99  fof(f3,axiom,(
% 3.55/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f22,plain,(
% 3.55/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f3])).
% 3.55/0.99  
% 3.55/0.99  fof(f9,axiom,(
% 3.55/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f28,plain,(
% 3.55/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f9])).
% 3.55/0.99  
% 3.55/0.99  fof(f10,axiom,(
% 3.55/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f29,plain,(
% 3.55/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f10])).
% 3.55/0.99  
% 3.55/0.99  fof(f11,axiom,(
% 3.55/0.99    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f30,plain,(
% 3.55/0.99    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f11])).
% 3.55/0.99  
% 3.55/0.99  fof(f36,plain,(
% 3.55/0.99    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.55/0.99    inference(definition_unfolding,[],[f29,f30])).
% 3.55/0.99  
% 3.55/0.99  fof(f37,plain,(
% 3.55/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.55/0.99    inference(definition_unfolding,[],[f28,f36])).
% 3.55/0.99  
% 3.55/0.99  fof(f43,plain,(
% 3.55/0.99    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 3.55/0.99    inference(definition_unfolding,[],[f22,f37,f37])).
% 3.55/0.99  
% 3.55/0.99  fof(f6,axiom,(
% 3.55/0.99    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f25,plain,(
% 3.55/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f6])).
% 3.55/0.99  
% 3.55/0.99  fof(f2,axiom,(
% 3.55/0.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f21,plain,(
% 3.55/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f2])).
% 3.55/0.99  
% 3.55/0.99  fof(f1,axiom,(
% 3.55/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f20,plain,(
% 3.55/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.55/0.99    inference(cnf_transformation,[],[f1])).
% 3.55/0.99  
% 3.55/0.99  fof(f35,plain,(
% 3.55/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.55/0.99    inference(definition_unfolding,[],[f21,f20])).
% 3.55/0.99  
% 3.55/0.99  fof(f8,axiom,(
% 3.55/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f27,plain,(
% 3.55/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.55/0.99    inference(cnf_transformation,[],[f8])).
% 3.55/0.99  
% 3.55/0.99  fof(f39,plain,(
% 3.55/0.99    ( ! [X0] : (k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.55/0.99    inference(definition_unfolding,[],[f27,f37])).
% 3.55/0.99  
% 3.55/0.99  fof(f44,plain,(
% 3.55/0.99    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3)))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.55/0.99    inference(definition_unfolding,[],[f25,f35,f30,f39])).
% 3.55/0.99  
% 3.55/0.99  fof(f15,conjecture,(
% 3.55/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 3.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.55/0.99  
% 3.55/0.99  fof(f16,negated_conjecture,(
% 3.55/0.99    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 3.55/0.99    inference(negated_conjecture,[],[f15])).
% 3.55/0.99  
% 3.55/0.99  fof(f17,plain,(
% 3.55/0.99    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2)),
% 3.55/0.99    inference(ennf_transformation,[],[f16])).
% 3.55/0.99  
% 3.55/0.99  fof(f18,plain,(
% 3.55/0.99    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2) => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2)),
% 3.55/0.99    introduced(choice_axiom,[])).
% 3.55/0.99  
% 3.55/0.99  fof(f19,plain,(
% 3.55/0.99    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2)),
% 3.55/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).
% 3.55/0.99  
% 3.55/0.99  fof(f34,plain,(
% 3.55/0.99    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2)),
% 3.55/0.99    inference(cnf_transformation,[],[f19])).
% 3.55/0.99  
% 3.55/0.99  fof(f47,plain,(
% 3.55/0.99    k3_enumset1(sK0,sK0,sK0,sK1,sK2) != k3_enumset1(sK1,sK1,sK1,sK0,sK2)),
% 3.55/0.99    inference(definition_unfolding,[],[f34,f36,f36])).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1,plain,
% 3.55/0.99      ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
% 3.55/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_18,plain,
% 3.55/0.99      ( k3_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35) = k3_enumset1(X1_35,X1_35,X1_35,X1_35,X0_35) ),
% 3.55/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_2,plain,
% 3.55/0.99      ( k5_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k5_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X0,X0,X1,X2,X3)))) = k3_enumset1(X0,X1,X2,X3,X4) ),
% 3.55/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_17,plain,
% 3.55/0.99      ( k5_xboole_0(k3_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35),k5_xboole_0(k3_enumset1(X4_35,X4_35,X4_35,X4_35,X4_35),k3_xboole_0(k3_enumset1(X4_35,X4_35,X4_35,X4_35,X4_35),k3_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35)))) = k3_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35) ),
% 3.55/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_86,plain,
% 3.55/0.99      ( k5_xboole_0(k3_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35),k5_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X2_35,X2_35),k3_xboole_0(k3_enumset1(X2_35,X2_35,X2_35,X2_35,X2_35),k3_enumset1(X0_35,X0_35,X0_35,X0_35,X1_35)))) = k3_enumset1(X1_35,X1_35,X1_35,X0_35,X2_35) ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_18,c_17]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1094,plain,
% 3.55/0.99      ( k3_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35) = k3_enumset1(X1_35,X1_35,X1_35,X0_35,X2_35) ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_86,c_17]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_5,negated_conjecture,
% 3.55/0.99      ( k3_enumset1(sK0,sK0,sK0,sK1,sK2) != k3_enumset1(sK1,sK1,sK1,sK0,sK2) ),
% 3.55/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_14,negated_conjecture,
% 3.55/0.99      ( k3_enumset1(sK0,sK0,sK0,sK1,sK2) != k3_enumset1(sK1,sK1,sK1,sK0,sK2) ),
% 3.55/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 3.55/0.99  
% 3.55/0.99  cnf(c_1590,plain,
% 3.55/0.99      ( $false ),
% 3.55/0.99      inference(superposition,[status(thm)],[c_1094,c_14]) ).
% 3.55/0.99  
% 3.55/0.99  
% 3.55/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.55/0.99  
% 3.55/0.99  ------                               Statistics
% 3.55/0.99  
% 3.55/0.99  ------ Selected
% 3.55/0.99  
% 3.55/0.99  total_time:                             0.116
% 3.55/0.99  
%------------------------------------------------------------------------------
