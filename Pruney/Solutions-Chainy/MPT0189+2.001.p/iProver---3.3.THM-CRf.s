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
% DateTime   : Thu Dec  3 11:27:51 EST 2020

% Result     : Theorem 7.98s
% Output     : CNFRefutation 7.98s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 179 expanded)
%              Number of clauses        :   13 (  17 expanded)
%              Number of leaves         :   13 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :   52 ( 180 expanded)
%              Number of equality atoms :   51 ( 179 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f42,f48])).

fof(f50,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f41,f49])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f50])).

fof(f56,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f29,f51,f51])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f28,f27])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k5_enumset1(X0,X0,X0,X0,X1,X2,X3)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f30,f47,f49,f49])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f45,f52])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k5_enumset1(X0,X0,X0,X1,X2,X3,X4)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f33,f47,f48,f51])).

fof(f21,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(negated_conjecture,[],[f21])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) ),
    inference(ennf_transformation,[],[f22])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f24])).

fof(f46,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK3) ),
    inference(definition_unfolding,[],[f46,f49,f49])).

cnf(c_2,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_30,plain,
    ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X0_36,X1_36) = k5_enumset1(X1_36,X1_36,X1_36,X1_36,X1_36,X1_36,X0_36) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_10,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_22,plain,
    ( k5_xboole_0(k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k5_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36,X5_36,X6_36),k3_xboole_0(k5_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36,X5_36,X6_36),k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36)))) = k5_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X5_36,X6_36) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_182,plain,
    ( k5_xboole_0(k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X0_36,X1_36),k5_xboole_0(k5_enumset1(X2_36,X2_36,X2_36,X2_36,X3_36,X4_36,X5_36),k3_xboole_0(k5_enumset1(X2_36,X2_36,X2_36,X2_36,X3_36,X4_36,X5_36),k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X0_36,X1_36)))) = k5_enumset1(X1_36,X1_36,X0_36,X2_36,X3_36,X4_36,X5_36) ),
    inference(superposition,[status(thm)],[c_30,c_22])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k5_enumset1(X0,X0,X0,X1,X2,X3,X4)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_32,plain,
    ( k5_xboole_0(k5_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36,X3_36,X4_36),k5_xboole_0(k5_enumset1(X5_36,X5_36,X5_36,X5_36,X5_36,X5_36,X6_36),k3_xboole_0(k5_enumset1(X5_36,X5_36,X5_36,X5_36,X5_36,X5_36,X6_36),k5_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36,X3_36,X4_36)))) = k5_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X5_36,X6_36) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_11537,plain,
    ( k5_enumset1(X0_36,X0_36,X1_36,X2_36,X2_36,X2_36,X3_36) = k5_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36,X2_36,X3_36) ),
    inference(superposition,[status(thm)],[c_182,c_32])).

cnf(c_318,plain,
    ( k5_enumset1(X0_36,X1_36,X2_36,X3_36,X3_36,X3_36,X4_36) = k5_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36,X3_36,X4_36) ),
    inference(superposition,[status(thm)],[c_32,c_22])).

cnf(c_11,negated_conjecture,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_21,negated_conjecture,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1721,plain,
    ( k5_enumset1(sK1,sK1,sK0,sK2,sK2,sK2,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_318,c_21])).

cnf(c_31507,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_11537,c_1721])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:38:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.98/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.98/1.48  
% 7.98/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.98/1.48  
% 7.98/1.48  ------  iProver source info
% 7.98/1.48  
% 7.98/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.98/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.98/1.48  git: non_committed_changes: false
% 7.98/1.48  git: last_make_outside_of_git: false
% 7.98/1.48  
% 7.98/1.48  ------ 
% 7.98/1.48  ------ Parsing...
% 7.98/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.98/1.48  
% 7.98/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 7.98/1.48  
% 7.98/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.98/1.48  
% 7.98/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.98/1.48  ------ Proving...
% 7.98/1.48  ------ Problem Properties 
% 7.98/1.48  
% 7.98/1.48  
% 7.98/1.48  clauses                                 12
% 7.98/1.48  conjectures                             1
% 7.98/1.48  EPR                                     0
% 7.98/1.48  Horn                                    12
% 7.98/1.48  unary                                   12
% 7.98/1.48  binary                                  0
% 7.98/1.48  lits                                    12
% 7.98/1.48  lits eq                                 12
% 7.98/1.48  fd_pure                                 0
% 7.98/1.48  fd_pseudo                               0
% 7.98/1.48  fd_cond                                 0
% 7.98/1.48  fd_pseudo_cond                          0
% 7.98/1.48  AC symbols                              0
% 7.98/1.48  
% 7.98/1.48  ------ Input Options Time Limit: Unbounded
% 7.98/1.48  
% 7.98/1.48  
% 7.98/1.48  ------ 
% 7.98/1.48  Current options:
% 7.98/1.48  ------ 
% 7.98/1.48  
% 7.98/1.48  
% 7.98/1.48  
% 7.98/1.48  
% 7.98/1.48  ------ Proving...
% 7.98/1.48  
% 7.98/1.48  
% 7.98/1.48  % SZS status Theorem for theBenchmark.p
% 7.98/1.48  
% 7.98/1.48   Resolution empty clause
% 7.98/1.48  
% 7.98/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.98/1.48  
% 7.98/1.48  fof(f4,axiom,(
% 7.98/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f29,plain,(
% 7.98/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f4])).
% 7.98/1.48  
% 7.98/1.48  fof(f15,axiom,(
% 7.98/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f40,plain,(
% 7.98/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f15])).
% 7.98/1.48  
% 7.98/1.48  fof(f16,axiom,(
% 7.98/1.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f41,plain,(
% 7.98/1.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f16])).
% 7.98/1.48  
% 7.98/1.48  fof(f17,axiom,(
% 7.98/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f42,plain,(
% 7.98/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f17])).
% 7.98/1.48  
% 7.98/1.48  fof(f18,axiom,(
% 7.98/1.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f43,plain,(
% 7.98/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f18])).
% 7.98/1.48  
% 7.98/1.48  fof(f19,axiom,(
% 7.98/1.48    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f44,plain,(
% 7.98/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f19])).
% 7.98/1.48  
% 7.98/1.48  fof(f48,plain,(
% 7.98/1.48    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 7.98/1.48    inference(definition_unfolding,[],[f43,f44])).
% 7.98/1.48  
% 7.98/1.48  fof(f49,plain,(
% 7.98/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 7.98/1.48    inference(definition_unfolding,[],[f42,f48])).
% 7.98/1.48  
% 7.98/1.48  fof(f50,plain,(
% 7.98/1.48    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 7.98/1.48    inference(definition_unfolding,[],[f41,f49])).
% 7.98/1.48  
% 7.98/1.48  fof(f51,plain,(
% 7.98/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 7.98/1.48    inference(definition_unfolding,[],[f40,f50])).
% 7.98/1.48  
% 7.98/1.48  fof(f56,plain,(
% 7.98/1.48    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0)) )),
% 7.98/1.48    inference(definition_unfolding,[],[f29,f51,f51])).
% 7.98/1.48  
% 7.98/1.48  fof(f20,axiom,(
% 7.98/1.48    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f45,plain,(
% 7.98/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f20])).
% 7.98/1.48  
% 7.98/1.48  fof(f5,axiom,(
% 7.98/1.48    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f30,plain,(
% 7.98/1.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f5])).
% 7.98/1.48  
% 7.98/1.48  fof(f3,axiom,(
% 7.98/1.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f28,plain,(
% 7.98/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.98/1.48    inference(cnf_transformation,[],[f3])).
% 7.98/1.48  
% 7.98/1.48  fof(f2,axiom,(
% 7.98/1.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f27,plain,(
% 7.98/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.98/1.48    inference(cnf_transformation,[],[f2])).
% 7.98/1.48  
% 7.98/1.48  fof(f47,plain,(
% 7.98/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 7.98/1.48    inference(definition_unfolding,[],[f28,f27])).
% 7.98/1.48  
% 7.98/1.48  fof(f52,plain,(
% 7.98/1.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k5_enumset1(X0,X0,X0,X0,X1,X2,X3)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 7.98/1.48    inference(definition_unfolding,[],[f30,f47,f49,f49])).
% 7.98/1.48  
% 7.98/1.48  fof(f64,plain,(
% 7.98/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 7.98/1.48    inference(definition_unfolding,[],[f45,f52])).
% 7.98/1.48  
% 7.98/1.48  fof(f8,axiom,(
% 7.98/1.48    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f33,plain,(
% 7.98/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 7.98/1.48    inference(cnf_transformation,[],[f8])).
% 7.98/1.48  
% 7.98/1.48  fof(f54,plain,(
% 7.98/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k5_enumset1(X0,X0,X0,X1,X2,X3,X4)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 7.98/1.48    inference(definition_unfolding,[],[f33,f47,f48,f51])).
% 7.98/1.48  
% 7.98/1.48  fof(f21,conjecture,(
% 7.98/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 7.98/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.98/1.48  
% 7.98/1.48  fof(f22,negated_conjecture,(
% 7.98/1.48    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 7.98/1.48    inference(negated_conjecture,[],[f21])).
% 7.98/1.48  
% 7.98/1.48  fof(f23,plain,(
% 7.98/1.48    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 7.98/1.48    inference(ennf_transformation,[],[f22])).
% 7.98/1.48  
% 7.98/1.48  fof(f24,plain,(
% 7.98/1.48    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 7.98/1.48    introduced(choice_axiom,[])).
% 7.98/1.48  
% 7.98/1.48  fof(f25,plain,(
% 7.98/1.48    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 7.98/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f24])).
% 7.98/1.48  
% 7.98/1.48  fof(f46,plain,(
% 7.98/1.48    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 7.98/1.48    inference(cnf_transformation,[],[f25])).
% 7.98/1.48  
% 7.98/1.48  fof(f65,plain,(
% 7.98/1.48    k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK3)),
% 7.98/1.48    inference(definition_unfolding,[],[f46,f49,f49])).
% 7.98/1.48  
% 7.98/1.48  cnf(c_2,plain,
% 7.98/1.48      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0) ),
% 7.98/1.48      inference(cnf_transformation,[],[f56]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_30,plain,
% 7.98/1.48      ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X0_36,X1_36) = k5_enumset1(X1_36,X1_36,X1_36,X1_36,X1_36,X1_36,X0_36) ),
% 7.98/1.48      inference(subtyping,[status(esa)],[c_2]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_10,plain,
% 7.98/1.48      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 7.98/1.48      inference(cnf_transformation,[],[f64]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_22,plain,
% 7.98/1.48      ( k5_xboole_0(k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36),k5_xboole_0(k5_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36,X5_36,X6_36),k3_xboole_0(k5_enumset1(X3_36,X3_36,X3_36,X3_36,X4_36,X5_36,X6_36),k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36)))) = k5_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X5_36,X6_36) ),
% 7.98/1.48      inference(subtyping,[status(esa)],[c_10]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_182,plain,
% 7.98/1.48      ( k5_xboole_0(k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X0_36,X1_36),k5_xboole_0(k5_enumset1(X2_36,X2_36,X2_36,X2_36,X3_36,X4_36,X5_36),k3_xboole_0(k5_enumset1(X2_36,X2_36,X2_36,X2_36,X3_36,X4_36,X5_36),k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X0_36,X1_36)))) = k5_enumset1(X1_36,X1_36,X0_36,X2_36,X3_36,X4_36,X5_36) ),
% 7.98/1.48      inference(superposition,[status(thm)],[c_30,c_22]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_0,plain,
% 7.98/1.48      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k5_enumset1(X0,X0,X0,X1,X2,X3,X4)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 7.98/1.48      inference(cnf_transformation,[],[f54]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_32,plain,
% 7.98/1.48      ( k5_xboole_0(k5_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36,X3_36,X4_36),k5_xboole_0(k5_enumset1(X5_36,X5_36,X5_36,X5_36,X5_36,X5_36,X6_36),k3_xboole_0(k5_enumset1(X5_36,X5_36,X5_36,X5_36,X5_36,X5_36,X6_36),k5_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36,X3_36,X4_36)))) = k5_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X5_36,X6_36) ),
% 7.98/1.48      inference(subtyping,[status(esa)],[c_0]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_11537,plain,
% 7.98/1.48      ( k5_enumset1(X0_36,X0_36,X1_36,X2_36,X2_36,X2_36,X3_36) = k5_enumset1(X1_36,X1_36,X1_36,X1_36,X0_36,X2_36,X3_36) ),
% 7.98/1.48      inference(superposition,[status(thm)],[c_182,c_32]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_318,plain,
% 7.98/1.48      ( k5_enumset1(X0_36,X1_36,X2_36,X3_36,X3_36,X3_36,X4_36) = k5_enumset1(X0_36,X0_36,X0_36,X1_36,X2_36,X3_36,X4_36) ),
% 7.98/1.48      inference(superposition,[status(thm)],[c_32,c_22]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_11,negated_conjecture,
% 7.98/1.48      ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK3) ),
% 7.98/1.48      inference(cnf_transformation,[],[f65]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_21,negated_conjecture,
% 7.98/1.48      ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK2,sK3) ),
% 7.98/1.48      inference(subtyping,[status(esa)],[c_11]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_1721,plain,
% 7.98/1.48      ( k5_enumset1(sK1,sK1,sK0,sK2,sK2,sK2,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) ),
% 7.98/1.48      inference(superposition,[status(thm)],[c_318,c_21]) ).
% 7.98/1.48  
% 7.98/1.48  cnf(c_31507,plain,
% 7.98/1.48      ( $false ),
% 7.98/1.48      inference(superposition,[status(thm)],[c_11537,c_1721]) ).
% 7.98/1.48  
% 7.98/1.48  
% 7.98/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.98/1.48  
% 7.98/1.48  ------                               Statistics
% 7.98/1.48  
% 7.98/1.48  ------ Selected
% 7.98/1.48  
% 7.98/1.48  total_time:                             0.99
% 7.98/1.48  
%------------------------------------------------------------------------------
