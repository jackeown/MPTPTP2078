%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:27:52 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:09:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.12/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/0.99  
% 2.12/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.12/0.99  
% 2.12/0.99  ------  iProver source info
% 2.12/0.99  
% 2.12/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.12/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.12/0.99  git: non_committed_changes: false
% 2.12/0.99  git: last_make_outside_of_git: false
% 2.12/0.99  
% 2.12/0.99  ------ 
% 2.12/0.99  ------ Parsing...
% 2.12/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.12/0.99  
% 2.12/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.12/0.99  
% 2.12/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.12/0.99  
% 2.12/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.12/0.99  ------ Proving...
% 2.12/0.99  ------ Problem Properties 
% 2.12/0.99  
% 2.12/0.99  
% 2.12/0.99  clauses                                 11
% 2.12/0.99  conjectures                             1
% 2.12/0.99  EPR                                     0
% 2.12/0.99  Horn                                    11
% 2.12/0.99  unary                                   11
% 2.12/0.99  binary                                  0
% 2.12/0.99  lits                                    11
% 2.12/0.99  lits eq                                 11
% 2.12/0.99  fd_pure                                 0
% 2.12/0.99  fd_pseudo                               0
% 2.12/0.99  fd_cond                                 0
% 2.12/0.99  fd_pseudo_cond                          0
% 2.12/0.99  AC symbols                              0
% 2.12/0.99  
% 2.12/0.99  ------ Input Options Time Limit: Unbounded
% 2.12/0.99  
% 2.12/0.99  
% 2.12/0.99  ------ 
% 2.12/0.99  Current options:
% 2.12/0.99  ------ 
% 2.12/0.99  
% 2.12/0.99  
% 2.12/0.99  
% 2.12/0.99  
% 2.12/0.99  ------ Proving...
% 2.12/0.99  
% 2.12/0.99  
% 2.12/0.99  % SZS status Theorem for theBenchmark.p
% 2.12/0.99  
% 2.12/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.12/0.99  
% 2.12/0.99  fof(f5,axiom,(
% 2.12/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 2.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.12/0.99  
% 2.12/0.99  fof(f28,plain,(
% 2.12/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 2.12/0.99    inference(cnf_transformation,[],[f5])).
% 2.12/0.99  
% 2.12/0.99  fof(f4,axiom,(
% 2.12/0.99    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 2.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.12/0.99  
% 2.12/0.99  fof(f27,plain,(
% 2.12/0.99    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.12/0.99    inference(cnf_transformation,[],[f4])).
% 2.12/0.99  
% 2.12/0.99  fof(f3,axiom,(
% 2.12/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.12/0.99  
% 2.12/0.99  fof(f26,plain,(
% 2.12/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.12/0.99    inference(cnf_transformation,[],[f3])).
% 2.12/0.99  
% 2.12/0.99  fof(f2,axiom,(
% 2.12/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.12/0.99  
% 2.12/0.99  fof(f25,plain,(
% 2.12/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.12/0.99    inference(cnf_transformation,[],[f2])).
% 2.12/0.99  
% 2.12/0.99  fof(f43,plain,(
% 2.12/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.12/0.99    inference(definition_unfolding,[],[f26,f25])).
% 2.12/0.99  
% 2.12/0.99  fof(f13,axiom,(
% 2.12/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.12/0.99  
% 2.12/0.99  fof(f36,plain,(
% 2.12/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.12/0.99    inference(cnf_transformation,[],[f13])).
% 2.12/0.99  
% 2.12/0.99  fof(f44,plain,(
% 2.12/0.99    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.12/0.99    inference(definition_unfolding,[],[f27,f43,f36,f36])).
% 2.12/0.99  
% 2.12/0.99  fof(f51,plain,(
% 2.12/0.99    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X3,X3,X2),k3_xboole_0(k1_enumset1(X3,X3,X2),k1_enumset1(X0,X0,X1))))) )),
% 2.12/0.99    inference(definition_unfolding,[],[f28,f44,f44])).
% 2.12/0.99  
% 2.12/0.99  fof(f1,axiom,(
% 2.12/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.12/0.99  
% 2.12/0.99  fof(f24,plain,(
% 2.12/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.12/0.99    inference(cnf_transformation,[],[f1])).
% 2.12/0.99  
% 2.12/0.99  fof(f50,plain,(
% 2.12/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 2.12/0.99    inference(definition_unfolding,[],[f24,f43,f43])).
% 2.12/0.99  
% 2.12/0.99  fof(f19,conjecture,(
% 2.12/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 2.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.12/0.99  
% 2.12/0.99  fof(f20,negated_conjecture,(
% 2.12/0.99    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 2.12/0.99    inference(negated_conjecture,[],[f19])).
% 2.12/0.99  
% 2.12/0.99  fof(f21,plain,(
% 2.12/0.99    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 2.12/0.99    inference(ennf_transformation,[],[f20])).
% 2.12/0.99  
% 2.12/0.99  fof(f22,plain,(
% 2.12/0.99    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 2.12/0.99    introduced(choice_axiom,[])).
% 2.12/0.99  
% 2.12/0.99  fof(f23,plain,(
% 2.12/0.99    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 2.12/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f22])).
% 2.12/0.99  
% 2.12/0.99  fof(f42,plain,(
% 2.12/0.99    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 2.12/0.99    inference(cnf_transformation,[],[f23])).
% 2.12/0.99  
% 2.12/0.99  fof(f58,plain,(
% 2.12/0.99    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1)))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0))))),
% 2.12/0.99    inference(definition_unfolding,[],[f42,f44,f44])).
% 2.12/0.99  
% 2.12/0.99  cnf(c_3,plain,
% 2.12/0.99      ( k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X2,X3),k3_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X3,X3,X2),k3_xboole_0(k1_enumset1(X3,X3,X2),k1_enumset1(X0,X0,X1)))) ),
% 2.12/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_31,plain,
% 2.12/0.99      ( k5_xboole_0(k1_enumset1(X0_37,X0_37,X1_37),k5_xboole_0(k1_enumset1(X2_37,X2_37,X3_37),k3_xboole_0(k1_enumset1(X2_37,X2_37,X3_37),k1_enumset1(X0_37,X0_37,X1_37)))) = k5_xboole_0(k1_enumset1(X0_37,X0_37,X1_37),k5_xboole_0(k1_enumset1(X3_37,X3_37,X2_37),k3_xboole_0(k1_enumset1(X3_37,X3_37,X2_37),k1_enumset1(X0_37,X0_37,X1_37)))) ),
% 2.12/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_328,plain,
% 2.12/0.99      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK3)))) ),
% 2.12/0.99      inference(instantiation,[status(thm)],[c_31]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_36,plain,
% 2.12/0.99      ( X0_36 != X1_36 | X2_36 != X1_36 | X2_36 = X0_36 ),
% 2.12/0.99      theory(equality) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_173,plain,
% 2.12/0.99      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)))) != X0_36
% 2.12/0.99      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) != X0_36
% 2.12/0.99      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)))) ),
% 2.12/0.99      inference(instantiation,[status(thm)],[c_36]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_327,plain,
% 2.12/0.99      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK3))))
% 2.12/0.99      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK3))))
% 2.12/0.99      | k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)))) ),
% 2.12/0.99      inference(instantiation,[status(thm)],[c_173]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_2,plain,
% 2.12/0.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 2.12/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_32,plain,
% 2.12/0.99      ( k5_xboole_0(X0_36,k5_xboole_0(X1_36,k3_xboole_0(X1_36,X0_36))) = k5_xboole_0(X1_36,k5_xboole_0(X0_36,k3_xboole_0(X0_36,X1_36))) ),
% 2.12/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_245,plain,
% 2.12/0.99      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k3_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK3)))) ),
% 2.12/0.99      inference(instantiation,[status(thm)],[c_32]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_114,plain,
% 2.12/0.99      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)))) ),
% 2.12/0.99      inference(instantiation,[status(thm)],[c_32]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_83,plain,
% 2.12/0.99      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) != X0_36
% 2.12/0.99      | k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1)))) != X0_36
% 2.12/0.99      | k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1)))) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) ),
% 2.12/0.99      inference(instantiation,[status(thm)],[c_36]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_113,plain,
% 2.12/0.99      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3))))
% 2.12/0.99      | k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1)))) != k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3))))
% 2.12/0.99      | k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1)))) = k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) ),
% 2.12/0.99      inference(instantiation,[status(thm)],[c_83]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_10,negated_conjecture,
% 2.12/0.99      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1)))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) ),
% 2.12/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(c_24,negated_conjecture,
% 2.12/0.99      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1)))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) ),
% 2.12/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 2.12/0.99  
% 2.12/0.99  cnf(contradiction,plain,
% 2.12/0.99      ( $false ),
% 2.12/0.99      inference(minisat,
% 2.12/0.99                [status(thm)],
% 2.12/0.99                [c_328,c_327,c_245,c_114,c_113,c_24]) ).
% 2.12/0.99  
% 2.12/0.99  
% 2.12/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.12/0.99  
% 2.12/0.99  ------                               Statistics
% 2.12/0.99  
% 2.12/0.99  ------ Selected
% 2.12/0.99  
% 2.12/0.99  total_time:                             0.069
% 2.12/0.99  
%------------------------------------------------------------------------------
