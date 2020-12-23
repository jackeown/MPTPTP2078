%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:10 EST 2020

% Result     : Theorem 15.30s
% Output     : CNFRefutation 15.30s
% Verified   : 
% Statistics : Number of formulae       :   51 (  79 expanded)
%              Number of clauses        :   26 (  31 expanded)
%              Number of leaves         :    8 (  17 expanded)
%              Depth                    :   12
%              Number of atoms          :   81 ( 148 expanded)
%              Number of equality atoms :   37 (  55 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k4_xboole_0(X1,X0),X2)
        & r1_tarski(k4_xboole_0(X0,X1),X2) )
     => r1_tarski(k5_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(k4_xboole_0(X1,X0),X2)
          & r1_tarski(k4_xboole_0(X0,X1),X2) )
       => r1_tarski(k5_xboole_0(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X1),X2)
      & r1_tarski(k4_xboole_0(X1,X0),X2)
      & r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X1),X2)
      & r1_tarski(k4_xboole_0(X1,X0),X2)
      & r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(flattening,[],[f13])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_xboole_0(X0,X1),X2)
        & r1_tarski(k4_xboole_0(X1,X0),X2)
        & r1_tarski(k4_xboole_0(X0,X1),X2) )
   => ( ~ r1_tarski(k5_xboole_0(sK0,sK1),sK2)
      & r1_tarski(k4_xboole_0(sK1,sK0),sK2)
      & r1_tarski(k4_xboole_0(sK0,sK1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK1),sK2)
    & r1_tarski(k4_xboole_0(sK1,sK0),sK2)
    & r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16])).

fof(f27,plain,(
    r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f28,plain,(
    r1_tarski(k4_xboole_0(sK1,sK0),sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f29,plain,(
    ~ r1_tarski(k5_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f31,plain,(
    ~ r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2) ),
    inference(definition_unfolding,[],[f29,f19])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1554,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_1559,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2095,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_1554,c_1559])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(k4_xboole_0(sK1,sK0),sK2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1555,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK0),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2094,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK0),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_1555,c_1559])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_6,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_1791,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_6,c_6])).

cnf(c_1796,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_1791,c_6])).

cnf(c_2390,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) = k4_xboole_0(X0,k2_xboole_0(X3,k2_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_0,c_1796])).

cnf(c_45797,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK2,k2_xboole_0(X1,k4_xboole_0(sK1,sK0)))) = k4_xboole_0(X0,k2_xboole_0(X1,sK2)) ),
    inference(superposition,[status(thm)],[c_2094,c_2390])).

cnf(c_5,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_1558,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_1561,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2263,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1558,c_1561])).

cnf(c_32677,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2263,c_6])).

cnf(c_48768,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(sK1,sK0)),k2_xboole_0(X0,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_45797,c_32677])).

cnf(c_53714,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2095,c_48768])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_1280,plain,
    ( r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2)
    | k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_8,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_53714,c_1280,c_8])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:57:14 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.30/2.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.30/2.51  
% 15.30/2.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.30/2.51  
% 15.30/2.51  ------  iProver source info
% 15.30/2.51  
% 15.30/2.51  git: date: 2020-06-30 10:37:57 +0100
% 15.30/2.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.30/2.51  git: non_committed_changes: false
% 15.30/2.51  git: last_make_outside_of_git: false
% 15.30/2.51  
% 15.30/2.51  ------ 
% 15.30/2.51  ------ Parsing...
% 15.30/2.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.30/2.51  
% 15.30/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 15.30/2.51  
% 15.30/2.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.30/2.51  
% 15.30/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.30/2.51  ------ Proving...
% 15.30/2.51  ------ Problem Properties 
% 15.30/2.51  
% 15.30/2.51  
% 15.30/2.51  clauses                                 11
% 15.30/2.51  conjectures                             3
% 15.30/2.51  EPR                                     0
% 15.30/2.51  Horn                                    11
% 15.30/2.51  unary                                   7
% 15.30/2.51  binary                                  4
% 15.30/2.51  lits                                    15
% 15.30/2.51  lits eq                                 6
% 15.30/2.51  fd_pure                                 0
% 15.30/2.51  fd_pseudo                               0
% 15.30/2.51  fd_cond                                 0
% 15.30/2.51  fd_pseudo_cond                          0
% 15.30/2.51  AC symbols                              0
% 15.30/2.51  
% 15.30/2.51  ------ Input Options Time Limit: Unbounded
% 15.30/2.51  
% 15.30/2.51  
% 15.30/2.51  
% 15.30/2.51  
% 15.30/2.51  ------ Preprocessing...
% 15.30/2.51  
% 15.30/2.51  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 15.30/2.51  Current options:
% 15.30/2.51  ------ 
% 15.30/2.51  
% 15.30/2.51  
% 15.30/2.51  
% 15.30/2.51  
% 15.30/2.51  ------ Proving...
% 15.30/2.51  
% 15.30/2.51  
% 15.30/2.51  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.30/2.51  
% 15.30/2.51  ------ Proving...
% 15.30/2.51  
% 15.30/2.51  
% 15.30/2.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.30/2.51  
% 15.30/2.51  ------ Proving...
% 15.30/2.51  
% 15.30/2.51  
% 15.30/2.51  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.30/2.51  
% 15.30/2.51  ------ Proving...
% 15.30/2.51  
% 15.30/2.51  
% 15.30/2.51  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.30/2.51  
% 15.30/2.51  ------ Proving...
% 15.30/2.51  
% 15.30/2.51  
% 15.30/2.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.30/2.51  
% 15.30/2.51  ------ Proving...
% 15.30/2.51  
% 15.30/2.51  
% 15.30/2.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.30/2.51  
% 15.30/2.51  ------ Proving...
% 15.30/2.51  
% 15.30/2.51  
% 15.30/2.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.30/2.51  
% 15.30/2.51  ------ Proving...
% 15.30/2.51  
% 15.30/2.51  
% 15.30/2.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.30/2.51  
% 15.30/2.51  ------ Proving...
% 15.30/2.51  
% 15.30/2.51  
% 15.30/2.51  % SZS status Theorem for theBenchmark.p
% 15.30/2.51  
% 15.30/2.51  % SZS output start CNFRefutation for theBenchmark.p
% 15.30/2.51  
% 15.30/2.51  fof(f9,conjecture,(
% 15.30/2.51    ! [X0,X1,X2] : ((r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2)) => r1_tarski(k5_xboole_0(X0,X1),X2))),
% 15.30/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.30/2.51  
% 15.30/2.51  fof(f10,negated_conjecture,(
% 15.30/2.51    ~! [X0,X1,X2] : ((r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2)) => r1_tarski(k5_xboole_0(X0,X1),X2))),
% 15.30/2.51    inference(negated_conjecture,[],[f9])).
% 15.30/2.51  
% 15.30/2.51  fof(f13,plain,(
% 15.30/2.51    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X1),X2) & (r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2)))),
% 15.30/2.51    inference(ennf_transformation,[],[f10])).
% 15.30/2.51  
% 15.30/2.51  fof(f14,plain,(
% 15.30/2.51    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X1),X2) & r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2))),
% 15.30/2.51    inference(flattening,[],[f13])).
% 15.30/2.51  
% 15.30/2.51  fof(f16,plain,(
% 15.30/2.51    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X1),X2) & r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2)) => (~r1_tarski(k5_xboole_0(sK0,sK1),sK2) & r1_tarski(k4_xboole_0(sK1,sK0),sK2) & r1_tarski(k4_xboole_0(sK0,sK1),sK2))),
% 15.30/2.51    introduced(choice_axiom,[])).
% 15.30/2.51  
% 15.30/2.51  fof(f17,plain,(
% 15.30/2.51    ~r1_tarski(k5_xboole_0(sK0,sK1),sK2) & r1_tarski(k4_xboole_0(sK1,sK0),sK2) & r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 15.30/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16])).
% 15.30/2.51  
% 15.30/2.51  fof(f27,plain,(
% 15.30/2.51    r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 15.30/2.51    inference(cnf_transformation,[],[f17])).
% 15.30/2.51  
% 15.30/2.51  fof(f5,axiom,(
% 15.30/2.51    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 15.30/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.30/2.51  
% 15.30/2.51  fof(f11,plain,(
% 15.30/2.51    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 15.30/2.51    inference(ennf_transformation,[],[f5])).
% 15.30/2.51  
% 15.30/2.51  fof(f23,plain,(
% 15.30/2.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 15.30/2.51    inference(cnf_transformation,[],[f11])).
% 15.30/2.51  
% 15.30/2.51  fof(f28,plain,(
% 15.30/2.51    r1_tarski(k4_xboole_0(sK1,sK0),sK2)),
% 15.30/2.51    inference(cnf_transformation,[],[f17])).
% 15.30/2.51  
% 15.30/2.51  fof(f1,axiom,(
% 15.30/2.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 15.30/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.30/2.51  
% 15.30/2.51  fof(f18,plain,(
% 15.30/2.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 15.30/2.51    inference(cnf_transformation,[],[f1])).
% 15.30/2.51  
% 15.30/2.51  fof(f7,axiom,(
% 15.30/2.51    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 15.30/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.30/2.51  
% 15.30/2.51  fof(f25,plain,(
% 15.30/2.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 15.30/2.51    inference(cnf_transformation,[],[f7])).
% 15.30/2.51  
% 15.30/2.51  fof(f6,axiom,(
% 15.30/2.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 15.30/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.30/2.51  
% 15.30/2.51  fof(f24,plain,(
% 15.30/2.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 15.30/2.51    inference(cnf_transformation,[],[f6])).
% 15.30/2.51  
% 15.30/2.51  fof(f3,axiom,(
% 15.30/2.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 15.30/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.30/2.51  
% 15.30/2.51  fof(f15,plain,(
% 15.30/2.51    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 15.30/2.51    inference(nnf_transformation,[],[f3])).
% 15.30/2.51  
% 15.30/2.51  fof(f21,plain,(
% 15.30/2.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 15.30/2.51    inference(cnf_transformation,[],[f15])).
% 15.30/2.51  
% 15.30/2.51  fof(f20,plain,(
% 15.30/2.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 15.30/2.51    inference(cnf_transformation,[],[f15])).
% 15.30/2.51  
% 15.30/2.51  fof(f29,plain,(
% 15.30/2.51    ~r1_tarski(k5_xboole_0(sK0,sK1),sK2)),
% 15.30/2.51    inference(cnf_transformation,[],[f17])).
% 15.30/2.51  
% 15.30/2.51  fof(f2,axiom,(
% 15.30/2.51    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 15.30/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.30/2.51  
% 15.30/2.51  fof(f19,plain,(
% 15.30/2.51    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 15.30/2.51    inference(cnf_transformation,[],[f2])).
% 15.30/2.51  
% 15.30/2.51  fof(f31,plain,(
% 15.30/2.51    ~r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2)),
% 15.30/2.51    inference(definition_unfolding,[],[f29,f19])).
% 15.30/2.51  
% 15.30/2.51  cnf(c_10,negated_conjecture,
% 15.30/2.51      ( r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
% 15.30/2.51      inference(cnf_transformation,[],[f27]) ).
% 15.30/2.51  
% 15.30/2.51  cnf(c_1554,plain,
% 15.30/2.51      ( r1_tarski(k4_xboole_0(sK0,sK1),sK2) = iProver_top ),
% 15.30/2.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.30/2.51  
% 15.30/2.51  cnf(c_4,plain,
% 15.30/2.51      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 15.30/2.51      inference(cnf_transformation,[],[f23]) ).
% 15.30/2.51  
% 15.30/2.51  cnf(c_1559,plain,
% 15.30/2.51      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 15.30/2.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.30/2.51  
% 15.30/2.51  cnf(c_2095,plain,
% 15.30/2.51      ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) = sK2 ),
% 15.30/2.51      inference(superposition,[status(thm)],[c_1554,c_1559]) ).
% 15.30/2.51  
% 15.30/2.51  cnf(c_9,negated_conjecture,
% 15.30/2.51      ( r1_tarski(k4_xboole_0(sK1,sK0),sK2) ),
% 15.30/2.51      inference(cnf_transformation,[],[f28]) ).
% 15.30/2.51  
% 15.30/2.51  cnf(c_1555,plain,
% 15.30/2.51      ( r1_tarski(k4_xboole_0(sK1,sK0),sK2) = iProver_top ),
% 15.30/2.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.30/2.51  
% 15.30/2.51  cnf(c_2094,plain,
% 15.30/2.51      ( k2_xboole_0(k4_xboole_0(sK1,sK0),sK2) = sK2 ),
% 15.30/2.51      inference(superposition,[status(thm)],[c_1555,c_1559]) ).
% 15.30/2.51  
% 15.30/2.51  cnf(c_0,plain,
% 15.30/2.51      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 15.30/2.51      inference(cnf_transformation,[],[f18]) ).
% 15.30/2.51  
% 15.30/2.51  cnf(c_6,plain,
% 15.30/2.51      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 15.30/2.51      inference(cnf_transformation,[],[f25]) ).
% 15.30/2.51  
% 15.30/2.51  cnf(c_1791,plain,
% 15.30/2.51      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 15.30/2.51      inference(superposition,[status(thm)],[c_6,c_6]) ).
% 15.30/2.51  
% 15.30/2.51  cnf(c_1796,plain,
% 15.30/2.51      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 15.30/2.51      inference(demodulation,[status(thm)],[c_1791,c_6]) ).
% 15.30/2.51  
% 15.30/2.51  cnf(c_2390,plain,
% 15.30/2.51      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) = k4_xboole_0(X0,k2_xboole_0(X3,k2_xboole_0(X1,X2))) ),
% 15.30/2.51      inference(superposition,[status(thm)],[c_0,c_1796]) ).
% 15.30/2.51  
% 15.30/2.51  cnf(c_45797,plain,
% 15.30/2.51      ( k4_xboole_0(X0,k2_xboole_0(sK2,k2_xboole_0(X1,k4_xboole_0(sK1,sK0)))) = k4_xboole_0(X0,k2_xboole_0(X1,sK2)) ),
% 15.30/2.51      inference(superposition,[status(thm)],[c_2094,c_2390]) ).
% 15.30/2.51  
% 15.30/2.51  cnf(c_5,plain,
% 15.30/2.51      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 15.30/2.51      inference(cnf_transformation,[],[f24]) ).
% 15.30/2.51  
% 15.30/2.51  cnf(c_1558,plain,
% 15.30/2.51      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 15.30/2.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.30/2.51  
% 15.30/2.51  cnf(c_1,plain,
% 15.30/2.51      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 15.30/2.51      inference(cnf_transformation,[],[f21]) ).
% 15.30/2.51  
% 15.30/2.51  cnf(c_1561,plain,
% 15.30/2.51      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 15.30/2.51      | r1_tarski(X0,X1) != iProver_top ),
% 15.30/2.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.30/2.51  
% 15.30/2.51  cnf(c_2263,plain,
% 15.30/2.51      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 15.30/2.51      inference(superposition,[status(thm)],[c_1558,c_1561]) ).
% 15.30/2.51  
% 15.30/2.51  cnf(c_32677,plain,
% 15.30/2.51      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 15.30/2.51      inference(superposition,[status(thm)],[c_2263,c_6]) ).
% 15.30/2.51  
% 15.30/2.51  cnf(c_48768,plain,
% 15.30/2.51      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(sK1,sK0)),k2_xboole_0(X0,sK2)) = k1_xboole_0 ),
% 15.30/2.51      inference(superposition,[status(thm)],[c_45797,c_32677]) ).
% 15.30/2.51  
% 15.30/2.51  cnf(c_53714,plain,
% 15.30/2.51      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2) = k1_xboole_0 ),
% 15.30/2.51      inference(superposition,[status(thm)],[c_2095,c_48768]) ).
% 15.30/2.51  
% 15.30/2.51  cnf(c_2,plain,
% 15.30/2.51      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 15.30/2.51      inference(cnf_transformation,[],[f20]) ).
% 15.30/2.51  
% 15.30/2.51  cnf(c_1280,plain,
% 15.30/2.51      ( r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2)
% 15.30/2.51      | k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2) != k1_xboole_0 ),
% 15.30/2.51      inference(instantiation,[status(thm)],[c_2]) ).
% 15.30/2.51  
% 15.30/2.51  cnf(c_8,negated_conjecture,
% 15.30/2.51      ( ~ r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2) ),
% 15.30/2.51      inference(cnf_transformation,[],[f31]) ).
% 15.30/2.51  
% 15.30/2.51  cnf(contradiction,plain,
% 15.30/2.51      ( $false ),
% 15.30/2.51      inference(minisat,[status(thm)],[c_53714,c_1280,c_8]) ).
% 15.30/2.51  
% 15.30/2.51  
% 15.30/2.51  % SZS output end CNFRefutation for theBenchmark.p
% 15.30/2.51  
% 15.30/2.51  ------                               Statistics
% 15.30/2.51  
% 15.30/2.51  ------ Selected
% 15.30/2.51  
% 15.30/2.51  total_time:                             1.73
% 15.30/2.51  
%------------------------------------------------------------------------------
