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
% DateTime   : Thu Dec  3 11:27:52 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 102 expanded)
%              Number of clauses        :   15 (  18 expanded)
%              Number of leaves         :    9 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   49 ( 115 expanded)
%              Number of equality atoms :   48 ( 114 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f27,f43,f36,f36])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X3,X3,X2),k3_xboole_0(k1_enumset1(X3,X3,X2),k1_enumset1(X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f28,f44,f44])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f43,f43])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(negated_conjecture,[],[f19])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) ),
    inference(ennf_transformation,[],[f20])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f22])).

fof(f42,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1)))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(definition_unfolding,[],[f42,f44,f44])).

cnf(c_3,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X3,X3,X2),k3_xboole_0(k1_enumset1(X3,X3,X2),k1_enumset1(X0,X0,X1)))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_31,plain,
    ( k5_xboole_0(k1_enumset1(X0_37,X0_37,X1_37),k5_xboole_0(k1_enumset1(X2_37,X2_37,X3_37),k3_xboole_0(k1_enumset1(X2_37,X2_37,X3_37),k1_enumset1(X0_37,X0_37,X1_37)))) = k5_xboole_0(k1_enumset1(X0_37,X0_37,X1_37),k5_xboole_0(k1_enumset1(X3_37,X3_37,X2_37),k3_xboole_0(k1_enumset1(X3_37,X3_37,X2_37),k1_enumset1(X0_37,X0_37,X1_37)))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_328,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK3)))) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_36,plain,
    ( X0_36 != X1_36
    | X2_36 != X1_36
    | X2_36 = X0_36 ),
    theory(equality)).

cnf(c_173,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)))) != X0_36
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) != X0_36
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)))) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_327,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK3))))
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK3))))
    | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)))) ),
    inference(instantiation,[status(thm)],[c_173])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_32,plain,
    ( k5_xboole_0(X0_36,k5_xboole_0(X1_36,k3_xboole_0(X1_36,X0_36))) = k5_xboole_0(X1_36,k5_xboole_0(X0_36,k3_xboole_0(X0_36,X1_36))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_245,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK3)))) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_114,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)))) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_83,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) != X0_36
    | k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1)))) != X0_36
    | k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1)))) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_113,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3))))
    | k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1)))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3))))
    | k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1)))) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(c_10,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1)))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_24,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1)))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_328,c_327,c_245,c_114,c_113,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:06:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 1.88/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.00  
% 1.88/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.88/1.00  
% 1.88/1.00  ------  iProver source info
% 1.88/1.00  
% 1.88/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.88/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.88/1.00  git: non_committed_changes: false
% 1.88/1.00  git: last_make_outside_of_git: false
% 1.88/1.00  
% 1.88/1.00  ------ 
% 1.88/1.00  ------ Parsing...
% 1.88/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.88/1.00  
% 1.88/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 1.88/1.00  
% 1.88/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.88/1.00  
% 1.88/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 1.88/1.00  ------ Proving...
% 1.88/1.00  ------ Problem Properties 
% 1.88/1.00  
% 1.88/1.00  
% 1.88/1.00  clauses                                 11
% 1.88/1.00  conjectures                             1
% 1.88/1.00  EPR                                     0
% 1.88/1.00  Horn                                    11
% 1.88/1.00  unary                                   11
% 1.88/1.00  binary                                  0
% 1.88/1.00  lits                                    11
% 1.88/1.00  lits eq                                 11
% 1.88/1.00  fd_pure                                 0
% 1.88/1.00  fd_pseudo                               0
% 1.88/1.00  fd_cond                                 0
% 1.88/1.00  fd_pseudo_cond                          0
% 1.88/1.00  AC symbols                              0
% 1.88/1.00  
% 1.88/1.00  ------ Input Options Time Limit: Unbounded
% 1.88/1.00  
% 1.88/1.00  
% 1.88/1.00  ------ 
% 1.88/1.00  Current options:
% 1.88/1.00  ------ 
% 1.88/1.00  
% 1.88/1.00  
% 1.88/1.00  
% 1.88/1.00  
% 1.88/1.00  ------ Proving...
% 1.88/1.00  
% 1.88/1.00  
% 1.88/1.00  % SZS status Theorem for theBenchmark.p
% 1.88/1.00  
% 1.88/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.88/1.00  
% 1.88/1.00  fof(f5,axiom,(
% 1.88/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 1.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.00  
% 1.88/1.00  fof(f28,plain,(
% 1.88/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 1.88/1.00    inference(cnf_transformation,[],[f5])).
% 1.88/1.00  
% 1.88/1.00  fof(f4,axiom,(
% 1.88/1.00    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 1.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.00  
% 1.88/1.00  fof(f27,plain,(
% 1.88/1.00    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.88/1.00    inference(cnf_transformation,[],[f4])).
% 1.88/1.00  
% 1.88/1.00  fof(f3,axiom,(
% 1.88/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.00  
% 1.88/1.00  fof(f26,plain,(
% 1.88/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.88/1.00    inference(cnf_transformation,[],[f3])).
% 1.88/1.00  
% 1.88/1.00  fof(f2,axiom,(
% 1.88/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.00  
% 1.88/1.00  fof(f25,plain,(
% 1.88/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.88/1.00    inference(cnf_transformation,[],[f2])).
% 1.88/1.00  
% 1.88/1.00  fof(f43,plain,(
% 1.88/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.88/1.00    inference(definition_unfolding,[],[f26,f25])).
% 1.88/1.00  
% 1.88/1.00  fof(f13,axiom,(
% 1.88/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.00  
% 1.88/1.00  fof(f36,plain,(
% 1.88/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.88/1.00    inference(cnf_transformation,[],[f13])).
% 1.88/1.00  
% 1.88/1.00  fof(f44,plain,(
% 1.88/1.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.88/1.00    inference(definition_unfolding,[],[f27,f43,f36,f36])).
% 1.88/1.00  
% 1.88/1.00  fof(f51,plain,(
% 1.88/1.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X3,X3,X2),k3_xboole_0(k1_enumset1(X3,X3,X2),k1_enumset1(X0,X0,X1))))) )),
% 1.88/1.00    inference(definition_unfolding,[],[f28,f44,f44])).
% 1.88/1.00  
% 1.88/1.00  fof(f1,axiom,(
% 1.88/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.00  
% 1.88/1.00  fof(f24,plain,(
% 1.88/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.88/1.00    inference(cnf_transformation,[],[f1])).
% 1.88/1.00  
% 1.88/1.00  fof(f50,plain,(
% 1.88/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.88/1.00    inference(definition_unfolding,[],[f24,f43,f43])).
% 1.88/1.00  
% 1.88/1.00  fof(f19,conjecture,(
% 1.88/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 1.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.00  
% 1.88/1.00  fof(f20,negated_conjecture,(
% 1.88/1.00    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 1.88/1.00    inference(negated_conjecture,[],[f19])).
% 1.88/1.00  
% 1.88/1.00  fof(f21,plain,(
% 1.88/1.00    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 1.88/1.00    inference(ennf_transformation,[],[f20])).
% 1.88/1.00  
% 1.88/1.00  fof(f22,plain,(
% 1.88/1.00    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 1.88/1.00    introduced(choice_axiom,[])).
% 1.88/1.00  
% 1.88/1.00  fof(f23,plain,(
% 1.88/1.00    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 1.88/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f22])).
% 1.88/1.00  
% 1.88/1.00  fof(f42,plain,(
% 1.88/1.00    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 1.88/1.00    inference(cnf_transformation,[],[f23])).
% 1.88/1.00  
% 1.88/1.00  fof(f58,plain,(
% 1.88/1.00    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1)))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0))))),
% 1.88/1.00    inference(definition_unfolding,[],[f42,f44,f44])).
% 1.88/1.00  
% 1.88/1.00  cnf(c_3,plain,
% 1.88/1.00      ( k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X3,X3,X2),k3_xboole_0(k1_enumset1(X3,X3,X2),k1_enumset1(X0,X0,X1)))) ),
% 1.88/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_31,plain,
% 1.88/1.00      ( k5_xboole_0(k1_enumset1(X0_37,X0_37,X1_37),k5_xboole_0(k1_enumset1(X2_37,X2_37,X3_37),k3_xboole_0(k1_enumset1(X2_37,X2_37,X3_37),k1_enumset1(X0_37,X0_37,X1_37)))) = k5_xboole_0(k1_enumset1(X0_37,X0_37,X1_37),k5_xboole_0(k1_enumset1(X3_37,X3_37,X2_37),k3_xboole_0(k1_enumset1(X3_37,X3_37,X2_37),k1_enumset1(X0_37,X0_37,X1_37)))) ),
% 1.88/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_328,plain,
% 1.88/1.00      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK3)))) ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_31]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_36,plain,
% 1.88/1.00      ( X0_36 != X1_36 | X2_36 != X1_36 | X2_36 = X0_36 ),
% 1.88/1.00      theory(equality) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_173,plain,
% 1.88/1.00      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)))) != X0_36
% 1.88/1.00      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) != X0_36
% 1.88/1.00      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)))) ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_36]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_327,plain,
% 1.88/1.00      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK3))))
% 1.88/1.00      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK3))))
% 1.88/1.00      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)))) ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_173]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_2,plain,
% 1.88/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 1.88/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_32,plain,
% 1.88/1.00      ( k5_xboole_0(X0_36,k5_xboole_0(X1_36,k3_xboole_0(X1_36,X0_36))) = k5_xboole_0(X1_36,k5_xboole_0(X0_36,k3_xboole_0(X0_36,X1_36))) ),
% 1.88/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_245,plain,
% 1.88/1.00      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK3)))) ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_32]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_114,plain,
% 1.88/1.00      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)))) ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_32]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_83,plain,
% 1.88/1.00      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) != X0_36
% 1.88/1.00      | k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1)))) != X0_36
% 1.88/1.00      | k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1)))) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_36]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_113,plain,
% 1.88/1.00      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3))))
% 1.88/1.00      | k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1)))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3))))
% 1.88/1.00      | k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1)))) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_83]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_10,negated_conjecture,
% 1.88/1.00      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1)))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) ),
% 1.88/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_24,negated_conjecture,
% 1.88/1.00      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1)))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) ),
% 1.88/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(contradiction,plain,
% 1.88/1.00      ( $false ),
% 1.88/1.00      inference(minisat,
% 1.88/1.00                [status(thm)],
% 1.88/1.00                [c_328,c_327,c_245,c_114,c_113,c_24]) ).
% 1.88/1.00  
% 1.88/1.00  
% 1.88/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.88/1.00  
% 1.88/1.00  ------                               Statistics
% 1.88/1.00  
% 1.88/1.00  ------ Selected
% 1.88/1.00  
% 1.88/1.00  total_time:                             0.059
% 1.88/1.00  
%------------------------------------------------------------------------------
