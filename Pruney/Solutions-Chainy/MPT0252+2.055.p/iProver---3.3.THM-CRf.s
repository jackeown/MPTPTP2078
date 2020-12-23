%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:29 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 256 expanded)
%              Number of clauses        :   33 (  91 expanded)
%              Number of leaves         :    8 (  53 expanded)
%              Depth                    :   16
%              Number of atoms          :  127 ( 610 expanded)
%              Number of equality atoms :   59 ( 207 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f29])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) ),
    inference(definition_unfolding,[],[f45,f54,f47,f47])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f70,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f40,f54])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f31])).

fof(f58,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK0,sK1),sK2)),sK2) ),
    inference(definition_unfolding,[],[f58,f54])).

fof(f59,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1529,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k2_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1526,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k2_tarski(X2,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1614,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1529,c_1526])).

cnf(c_0,plain,
    ( k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_9,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1528,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1595,plain,
    ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1528])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k2_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1525,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k2_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1604,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1595,c_1525])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k2_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1527,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r1_tarski(k2_tarski(X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1530,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1656,plain,
    ( k2_tarski(X0,X1) = X2
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_tarski(X2,k2_tarski(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1527,c_1530])).

cnf(c_1754,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X2,X3)
    | r2_hidden(X1,k2_tarski(X2,X3)) != iProver_top
    | r2_hidden(X0,k2_tarski(X2,X3)) != iProver_top
    | r2_hidden(X3,k2_tarski(X0,X1)) != iProver_top
    | r2_hidden(X2,k2_tarski(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1527,c_1656])).

cnf(c_1777,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X2,X0)
    | r2_hidden(X0,k2_tarski(X2,X0)) != iProver_top
    | r2_hidden(X2,k2_tarski(X0,X1)) != iProver_top
    | r2_hidden(X1,k2_tarski(X2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1604,c_1754])).

cnf(c_1802,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X2)
    | r2_hidden(X0,k2_tarski(X1,X2)) != iProver_top
    | r2_hidden(X2,k2_tarski(X0,X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1777,c_1614])).

cnf(c_1805,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | r2_hidden(X1,k2_tarski(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1614,c_1802])).

cnf(c_1814,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1805,c_1604])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK0,sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1523,plain,
    ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK0,sK1),sK2)),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1816,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK2,k2_tarski(sK0,sK1))),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1814,c_1523])).

cnf(c_1628,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = X0
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1528,c_1530])).

cnf(c_1970,plain,
    ( k3_tarski(k2_tarski(sK2,k2_tarski(sK0,sK1))) = sK2 ),
    inference(superposition,[status(thm)],[c_1816,c_1628])).

cnf(c_1848,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1814,c_1528])).

cnf(c_1980,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1970,c_1848])).

cnf(c_1988,plain,
    ( r2_hidden(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1980,c_1525])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_20,plain,
    ( r2_hidden(sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1988,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:22:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.31/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.02  
% 3.31/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.31/1.02  
% 3.31/1.02  ------  iProver source info
% 3.31/1.02  
% 3.31/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.31/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.31/1.02  git: non_committed_changes: false
% 3.31/1.02  git: last_make_outside_of_git: false
% 3.31/1.02  
% 3.31/1.02  ------ 
% 3.31/1.02  ------ Parsing...
% 3.31/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.31/1.02  
% 3.31/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.31/1.02  
% 3.31/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.31/1.02  
% 3.31/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.31/1.02  ------ Proving...
% 3.31/1.02  ------ Problem Properties 
% 3.31/1.02  
% 3.31/1.02  
% 3.31/1.02  clauses                                 18
% 3.31/1.02  conjectures                             2
% 3.31/1.02  EPR                                     3
% 3.31/1.02  Horn                                    18
% 3.31/1.02  unary                                   14
% 3.31/1.02  binary                                  2
% 3.31/1.02  lits                                    24
% 3.31/1.02  lits eq                                 10
% 3.31/1.02  fd_pure                                 0
% 3.31/1.02  fd_pseudo                               0
% 3.31/1.02  fd_cond                                 0
% 3.31/1.02  fd_pseudo_cond                          1
% 3.31/1.02  AC symbols                              1
% 3.31/1.02  
% 3.31/1.02  ------ Input Options Time Limit: Unbounded
% 3.31/1.02  
% 3.31/1.02  
% 3.31/1.02  
% 3.31/1.02  
% 3.31/1.02  ------ Preprocessing...
% 3.31/1.02  
% 3.31/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.31/1.02  Current options:
% 3.31/1.02  ------ 
% 3.31/1.02  
% 3.31/1.02  
% 3.31/1.02  
% 3.31/1.02  
% 3.31/1.02  ------ Proving...
% 3.31/1.02  
% 3.31/1.02  
% 3.31/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.31/1.02  
% 3.31/1.02  ------ Proving...
% 3.31/1.02  
% 3.31/1.02  
% 3.31/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.31/1.02  
% 3.31/1.02  ------ Proving...
% 3.31/1.02  
% 3.31/1.02  
% 3.31/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.31/1.02  
% 3.31/1.02  ------ Proving...
% 3.31/1.02  
% 3.31/1.02  
% 3.31/1.02  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.31/1.02  
% 3.31/1.02  ------ Proving...
% 3.31/1.02  
% 3.31/1.02  
% 3.31/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.31/1.02  
% 3.31/1.02  ------ Proving...
% 3.31/1.02  
% 3.31/1.02  
% 3.31/1.02  % SZS status Theorem for theBenchmark.p
% 3.31/1.02  
% 3.31/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.31/1.02  
% 3.31/1.02  fof(f4,axiom,(
% 3.31/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.31/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.02  
% 3.31/1.02  fof(f27,plain,(
% 3.31/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.31/1.02    inference(nnf_transformation,[],[f4])).
% 3.31/1.02  
% 3.31/1.02  fof(f28,plain,(
% 3.31/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.31/1.02    inference(flattening,[],[f27])).
% 3.31/1.02  
% 3.31/1.02  fof(f37,plain,(
% 3.31/1.02    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.31/1.02    inference(cnf_transformation,[],[f28])).
% 3.31/1.02  
% 3.31/1.02  fof(f74,plain,(
% 3.31/1.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.31/1.02    inference(equality_resolution,[],[f37])).
% 3.31/1.02  
% 3.31/1.02  fof(f21,axiom,(
% 3.31/1.02    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.31/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.02  
% 3.31/1.02  fof(f29,plain,(
% 3.31/1.02    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.31/1.02    inference(nnf_transformation,[],[f21])).
% 3.31/1.02  
% 3.31/1.02  fof(f30,plain,(
% 3.31/1.02    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.31/1.02    inference(flattening,[],[f29])).
% 3.31/1.02  
% 3.31/1.02  fof(f56,plain,(
% 3.31/1.02    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.31/1.02    inference(cnf_transformation,[],[f30])).
% 3.31/1.02  
% 3.31/1.02  fof(f11,axiom,(
% 3.31/1.02    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 3.31/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.02  
% 3.31/1.02  fof(f45,plain,(
% 3.31/1.02    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 3.31/1.02    inference(cnf_transformation,[],[f11])).
% 3.31/1.02  
% 3.31/1.02  fof(f20,axiom,(
% 3.31/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.31/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.02  
% 3.31/1.02  fof(f54,plain,(
% 3.31/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.31/1.02    inference(cnf_transformation,[],[f20])).
% 3.31/1.02  
% 3.31/1.02  fof(f13,axiom,(
% 3.31/1.02    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.31/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.02  
% 3.31/1.02  fof(f47,plain,(
% 3.31/1.02    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.31/1.02    inference(cnf_transformation,[],[f13])).
% 3.31/1.02  
% 3.31/1.02  fof(f65,plain,(
% 3.31/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1)))) )),
% 3.31/1.02    inference(definition_unfolding,[],[f45,f54,f47,f47])).
% 3.31/1.02  
% 3.31/1.02  fof(f6,axiom,(
% 3.31/1.02    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.31/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.02  
% 3.31/1.02  fof(f40,plain,(
% 3.31/1.02    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.31/1.02    inference(cnf_transformation,[],[f6])).
% 3.31/1.02  
% 3.31/1.02  fof(f70,plain,(
% 3.31/1.02    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 3.31/1.02    inference(definition_unfolding,[],[f40,f54])).
% 3.31/1.02  
% 3.31/1.02  fof(f55,plain,(
% 3.31/1.02    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.31/1.02    inference(cnf_transformation,[],[f30])).
% 3.31/1.02  
% 3.31/1.02  fof(f57,plain,(
% 3.31/1.02    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.31/1.02    inference(cnf_transformation,[],[f30])).
% 3.31/1.02  
% 3.31/1.02  fof(f38,plain,(
% 3.31/1.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.31/1.02    inference(cnf_transformation,[],[f28])).
% 3.31/1.02  
% 3.31/1.02  fof(f22,conjecture,(
% 3.31/1.02    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 3.31/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/1.02  
% 3.31/1.02  fof(f23,negated_conjecture,(
% 3.31/1.02    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 3.31/1.02    inference(negated_conjecture,[],[f22])).
% 3.31/1.02  
% 3.31/1.02  fof(f26,plain,(
% 3.31/1.02    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 3.31/1.02    inference(ennf_transformation,[],[f23])).
% 3.31/1.02  
% 3.31/1.02  fof(f31,plain,(
% 3.31/1.02    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 3.31/1.02    introduced(choice_axiom,[])).
% 3.31/1.02  
% 3.31/1.02  fof(f32,plain,(
% 3.31/1.02    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 3.31/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f31])).
% 3.31/1.02  
% 3.31/1.02  fof(f58,plain,(
% 3.31/1.02    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 3.31/1.02    inference(cnf_transformation,[],[f32])).
% 3.31/1.02  
% 3.31/1.02  fof(f73,plain,(
% 3.31/1.02    r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK0,sK1),sK2)),sK2)),
% 3.31/1.02    inference(definition_unfolding,[],[f58,f54])).
% 3.31/1.02  
% 3.31/1.02  fof(f59,plain,(
% 3.31/1.02    ~r2_hidden(sK0,sK2)),
% 3.31/1.02    inference(cnf_transformation,[],[f32])).
% 3.31/1.02  
% 3.31/1.02  cnf(c_6,plain,
% 3.31/1.02      ( r1_tarski(X0,X0) ),
% 3.31/1.02      inference(cnf_transformation,[],[f74]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_1529,plain,
% 3.31/1.02      ( r1_tarski(X0,X0) = iProver_top ),
% 3.31/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_15,plain,
% 3.31/1.02      ( r2_hidden(X0,X1) | ~ r1_tarski(k2_tarski(X2,X0),X1) ),
% 3.31/1.02      inference(cnf_transformation,[],[f56]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_1526,plain,
% 3.31/1.02      ( r2_hidden(X0,X1) = iProver_top
% 3.31/1.02      | r1_tarski(k2_tarski(X2,X0),X1) != iProver_top ),
% 3.31/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_1614,plain,
% 3.31/1.02      ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
% 3.31/1.02      inference(superposition,[status(thm)],[c_1529,c_1526]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_0,plain,
% 3.31/1.02      ( k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X0,X1) ),
% 3.31/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_9,plain,
% 3.31/1.02      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
% 3.31/1.02      inference(cnf_transformation,[],[f70]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_1528,plain,
% 3.31/1.02      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
% 3.31/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_1595,plain,
% 3.31/1.02      ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) = iProver_top ),
% 3.31/1.02      inference(superposition,[status(thm)],[c_0,c_1528]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_16,plain,
% 3.31/1.02      ( r2_hidden(X0,X1) | ~ r1_tarski(k2_tarski(X0,X2),X1) ),
% 3.31/1.02      inference(cnf_transformation,[],[f55]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_1525,plain,
% 3.31/1.02      ( r2_hidden(X0,X1) = iProver_top
% 3.31/1.02      | r1_tarski(k2_tarski(X0,X2),X1) != iProver_top ),
% 3.31/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_1604,plain,
% 3.31/1.02      ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
% 3.31/1.02      inference(superposition,[status(thm)],[c_1595,c_1525]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_14,plain,
% 3.31/1.02      ( ~ r2_hidden(X0,X1)
% 3.31/1.02      | ~ r2_hidden(X2,X1)
% 3.31/1.02      | r1_tarski(k2_tarski(X2,X0),X1) ),
% 3.31/1.02      inference(cnf_transformation,[],[f57]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_1527,plain,
% 3.31/1.02      ( r2_hidden(X0,X1) != iProver_top
% 3.31/1.02      | r2_hidden(X2,X1) != iProver_top
% 3.31/1.02      | r1_tarski(k2_tarski(X2,X0),X1) = iProver_top ),
% 3.31/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_5,plain,
% 3.31/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.31/1.02      inference(cnf_transformation,[],[f38]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_1530,plain,
% 3.31/1.02      ( X0 = X1
% 3.31/1.02      | r1_tarski(X0,X1) != iProver_top
% 3.31/1.02      | r1_tarski(X1,X0) != iProver_top ),
% 3.31/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_1656,plain,
% 3.31/1.02      ( k2_tarski(X0,X1) = X2
% 3.31/1.02      | r2_hidden(X1,X2) != iProver_top
% 3.31/1.02      | r2_hidden(X0,X2) != iProver_top
% 3.31/1.02      | r1_tarski(X2,k2_tarski(X0,X1)) != iProver_top ),
% 3.31/1.02      inference(superposition,[status(thm)],[c_1527,c_1530]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_1754,plain,
% 3.31/1.02      ( k2_tarski(X0,X1) = k2_tarski(X2,X3)
% 3.31/1.02      | r2_hidden(X1,k2_tarski(X2,X3)) != iProver_top
% 3.31/1.02      | r2_hidden(X0,k2_tarski(X2,X3)) != iProver_top
% 3.31/1.02      | r2_hidden(X3,k2_tarski(X0,X1)) != iProver_top
% 3.31/1.02      | r2_hidden(X2,k2_tarski(X0,X1)) != iProver_top ),
% 3.31/1.02      inference(superposition,[status(thm)],[c_1527,c_1656]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_1777,plain,
% 3.31/1.02      ( k2_tarski(X0,X1) = k2_tarski(X2,X0)
% 3.31/1.02      | r2_hidden(X0,k2_tarski(X2,X0)) != iProver_top
% 3.31/1.02      | r2_hidden(X2,k2_tarski(X0,X1)) != iProver_top
% 3.31/1.02      | r2_hidden(X1,k2_tarski(X2,X0)) != iProver_top ),
% 3.31/1.02      inference(superposition,[status(thm)],[c_1604,c_1754]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_1802,plain,
% 3.31/1.02      ( k2_tarski(X0,X1) = k2_tarski(X1,X2)
% 3.31/1.02      | r2_hidden(X0,k2_tarski(X1,X2)) != iProver_top
% 3.31/1.02      | r2_hidden(X2,k2_tarski(X0,X1)) != iProver_top ),
% 3.31/1.02      inference(forward_subsumption_resolution,
% 3.31/1.02                [status(thm)],
% 3.31/1.02                [c_1777,c_1614]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_1805,plain,
% 3.31/1.02      ( k2_tarski(X0,X1) = k2_tarski(X1,X0)
% 3.31/1.02      | r2_hidden(X1,k2_tarski(X1,X0)) != iProver_top ),
% 3.31/1.02      inference(superposition,[status(thm)],[c_1614,c_1802]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_1814,plain,
% 3.31/1.02      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 3.31/1.02      inference(forward_subsumption_resolution,
% 3.31/1.02                [status(thm)],
% 3.31/1.02                [c_1805,c_1604]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_18,negated_conjecture,
% 3.31/1.02      ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK0,sK1),sK2)),sK2) ),
% 3.31/1.02      inference(cnf_transformation,[],[f73]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_1523,plain,
% 3.31/1.02      ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK0,sK1),sK2)),sK2) = iProver_top ),
% 3.31/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_1816,plain,
% 3.31/1.02      ( r1_tarski(k3_tarski(k2_tarski(sK2,k2_tarski(sK0,sK1))),sK2) = iProver_top ),
% 3.31/1.02      inference(demodulation,[status(thm)],[c_1814,c_1523]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_1628,plain,
% 3.31/1.02      ( k3_tarski(k2_tarski(X0,X1)) = X0
% 3.31/1.02      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),X0) != iProver_top ),
% 3.31/1.02      inference(superposition,[status(thm)],[c_1528,c_1530]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_1970,plain,
% 3.31/1.02      ( k3_tarski(k2_tarski(sK2,k2_tarski(sK0,sK1))) = sK2 ),
% 3.31/1.02      inference(superposition,[status(thm)],[c_1816,c_1628]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_1848,plain,
% 3.31/1.02      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
% 3.31/1.02      inference(superposition,[status(thm)],[c_1814,c_1528]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_1980,plain,
% 3.31/1.02      ( r1_tarski(k2_tarski(sK0,sK1),sK2) = iProver_top ),
% 3.31/1.02      inference(superposition,[status(thm)],[c_1970,c_1848]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_1988,plain,
% 3.31/1.02      ( r2_hidden(sK0,sK2) = iProver_top ),
% 3.31/1.02      inference(superposition,[status(thm)],[c_1980,c_1525]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_17,negated_conjecture,
% 3.31/1.02      ( ~ r2_hidden(sK0,sK2) ),
% 3.31/1.02      inference(cnf_transformation,[],[f59]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(c_20,plain,
% 3.31/1.02      ( r2_hidden(sK0,sK2) != iProver_top ),
% 3.31/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.31/1.02  
% 3.31/1.02  cnf(contradiction,plain,
% 3.31/1.02      ( $false ),
% 3.31/1.02      inference(minisat,[status(thm)],[c_1988,c_20]) ).
% 3.31/1.02  
% 3.31/1.02  
% 3.31/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.31/1.02  
% 3.31/1.02  ------                               Statistics
% 3.31/1.02  
% 3.31/1.02  ------ Selected
% 3.31/1.02  
% 3.31/1.02  total_time:                             0.086
% 3.31/1.02  
%------------------------------------------------------------------------------
