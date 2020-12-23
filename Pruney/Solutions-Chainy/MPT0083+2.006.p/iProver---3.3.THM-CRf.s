%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:09 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 134 expanded)
%              Number of clauses        :   31 (  47 expanded)
%              Number of leaves         :   10 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  106 ( 231 expanded)
%              Number of equality atoms :   39 ( 106 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f14,f18,f18])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f17,f18])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f15,f18])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f16,f18])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
        & r1_xboole_0(X0,X1) )
   => ( ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f12])).

fof(f21,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f26,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
    inference(definition_unfolding,[],[f21,f18,f18])).

fof(f20,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_155,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_158,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_901,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_155,c_158])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_1078,plain,
    ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
    | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(resolution,[status(thm)],[c_901,c_0])).

cnf(c_3,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_87,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X0 != X3
    | k4_xboole_0(X3,k4_xboole_0(X3,X4)) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_4])).

cnf(c_88,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X1) ),
    inference(unflattening,[status(thm)],[c_87])).

cnf(c_2090,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X0)),X1) ),
    inference(resolution,[status(thm)],[c_1078,c_88])).

cnf(c_156,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_915,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_156,c_155])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_923,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(resolution,[status(thm)],[c_915,c_2])).

cnf(c_909,plain,
    ( X0 != k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | k4_xboole_0(X2,k4_xboole_0(X2,X1)) = X0 ),
    inference(resolution,[status(thm)],[c_156,c_0])).

cnf(c_1201,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X1,k4_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_923,c_909])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_1209,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(resolution,[status(thm)],[c_1201,c_1])).

cnf(c_2317,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0))) ),
    inference(resolution,[status(thm)],[c_2090,c_1209])).

cnf(c_5,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_2319,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
    inference(resolution,[status(thm)],[c_2090,c_5])).

cnf(c_2467,plain,
    ( ~ r1_xboole_0(sK1,sK0) ),
    inference(resolution,[status(thm)],[c_2317,c_2319])).

cnf(c_6,negated_conjecture,
    ( r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_306,plain,
    ( r1_xboole_0(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_308,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_437,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_306,c_308])).

cnf(c_309,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_496,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_309])).

cnf(c_650,plain,
    ( r1_xboole_0(sK1,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_437,c_496])).

cnf(c_664,plain,
    ( r1_xboole_0(sK1,sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_650])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2467,c_664])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:56:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.24/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/0.99  
% 3.24/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.24/0.99  
% 3.24/0.99  ------  iProver source info
% 3.24/0.99  
% 3.24/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.24/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.24/0.99  git: non_committed_changes: false
% 3.24/0.99  git: last_make_outside_of_git: false
% 3.24/0.99  
% 3.24/0.99  ------ 
% 3.24/0.99  ------ Parsing...
% 3.24/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.24/0.99  
% 3.24/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.24/0.99  
% 3.24/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.24/0.99  
% 3.24/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.24/0.99  ------ Proving...
% 3.24/0.99  ------ Problem Properties 
% 3.24/0.99  
% 3.24/0.99  
% 3.24/0.99  clauses                                 6
% 3.24/0.99  conjectures                             2
% 3.24/0.99  EPR                                     1
% 3.24/0.99  Horn                                    6
% 3.24/0.99  unary                                   3
% 3.24/0.99  binary                                  3
% 3.24/0.99  lits                                    9
% 3.24/0.99  lits eq                                 3
% 3.24/0.99  fd_pure                                 0
% 3.24/0.99  fd_pseudo                               0
% 3.24/0.99  fd_cond                                 0
% 3.24/0.99  fd_pseudo_cond                          0
% 3.24/0.99  AC symbols                              0
% 3.24/0.99  
% 3.24/0.99  ------ Input Options Time Limit: Unbounded
% 3.24/0.99  
% 3.24/0.99  
% 3.24/0.99  ------ 
% 3.24/0.99  Current options:
% 3.24/0.99  ------ 
% 3.24/0.99  
% 3.24/0.99  
% 3.24/0.99  
% 3.24/0.99  
% 3.24/0.99  ------ Proving...
% 3.24/0.99  
% 3.24/0.99  
% 3.24/0.99  % SZS status Theorem for theBenchmark.p
% 3.24/0.99  
% 3.24/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.24/0.99  
% 3.24/0.99  fof(f1,axiom,(
% 3.24/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.24/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/0.99  
% 3.24/0.99  fof(f14,plain,(
% 3.24/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.24/0.99    inference(cnf_transformation,[],[f1])).
% 3.24/0.99  
% 3.24/0.99  fof(f4,axiom,(
% 3.24/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.24/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/0.99  
% 3.24/0.99  fof(f18,plain,(
% 3.24/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.24/0.99    inference(cnf_transformation,[],[f4])).
% 3.24/0.99  
% 3.24/0.99  fof(f22,plain,(
% 3.24/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.24/0.99    inference(definition_unfolding,[],[f14,f18,f18])).
% 3.24/0.99  
% 3.24/0.99  fof(f3,axiom,(
% 3.24/0.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.24/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/0.99  
% 3.24/0.99  fof(f17,plain,(
% 3.24/0.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.24/0.99    inference(cnf_transformation,[],[f3])).
% 3.24/0.99  
% 3.24/0.99  fof(f25,plain,(
% 3.24/0.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 3.24/0.99    inference(definition_unfolding,[],[f17,f18])).
% 3.24/0.99  
% 3.24/0.99  fof(f5,axiom,(
% 3.24/0.99    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 3.24/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/0.99  
% 3.24/0.99  fof(f8,plain,(
% 3.24/0.99    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.24/0.99    inference(ennf_transformation,[],[f5])).
% 3.24/0.99  
% 3.24/0.99  fof(f9,plain,(
% 3.24/0.99    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 3.24/0.99    inference(flattening,[],[f8])).
% 3.24/0.99  
% 3.24/0.99  fof(f19,plain,(
% 3.24/0.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.24/0.99    inference(cnf_transformation,[],[f9])).
% 3.24/0.99  
% 3.24/0.99  fof(f2,axiom,(
% 3.24/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.24/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/0.99  
% 3.24/0.99  fof(f11,plain,(
% 3.24/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.24/0.99    inference(nnf_transformation,[],[f2])).
% 3.24/0.99  
% 3.24/0.99  fof(f15,plain,(
% 3.24/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.24/0.99    inference(cnf_transformation,[],[f11])).
% 3.24/0.99  
% 3.24/0.99  fof(f24,plain,(
% 3.24/0.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.24/0.99    inference(definition_unfolding,[],[f15,f18])).
% 3.24/0.99  
% 3.24/0.99  fof(f16,plain,(
% 3.24/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.24/0.99    inference(cnf_transformation,[],[f11])).
% 3.24/0.99  
% 3.24/0.99  fof(f23,plain,(
% 3.24/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.24/0.99    inference(definition_unfolding,[],[f16,f18])).
% 3.24/0.99  
% 3.24/0.99  fof(f6,conjecture,(
% 3.24/0.99    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 3.24/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/0.99  
% 3.24/0.99  fof(f7,negated_conjecture,(
% 3.24/0.99    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 3.24/0.99    inference(negated_conjecture,[],[f6])).
% 3.24/0.99  
% 3.24/0.99  fof(f10,plain,(
% 3.24/0.99    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1))),
% 3.24/0.99    inference(ennf_transformation,[],[f7])).
% 3.24/0.99  
% 3.24/0.99  fof(f12,plain,(
% 3.24/0.99    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1)) => (~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) & r1_xboole_0(sK0,sK1))),
% 3.24/0.99    introduced(choice_axiom,[])).
% 3.24/0.99  
% 3.24/0.99  fof(f13,plain,(
% 3.24/0.99    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) & r1_xboole_0(sK0,sK1)),
% 3.24/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f12])).
% 3.24/0.99  
% 3.24/0.99  fof(f21,plain,(
% 3.24/0.99    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))),
% 3.24/0.99    inference(cnf_transformation,[],[f13])).
% 3.24/0.99  
% 3.24/0.99  fof(f26,plain,(
% 3.24/0.99    ~r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))),
% 3.24/0.99    inference(definition_unfolding,[],[f21,f18,f18])).
% 3.24/0.99  
% 3.24/0.99  fof(f20,plain,(
% 3.24/0.99    r1_xboole_0(sK0,sK1)),
% 3.24/0.99    inference(cnf_transformation,[],[f13])).
% 3.24/0.99  
% 3.24/0.99  cnf(c_155,plain,( X0 = X0 ),theory(equality) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_158,plain,
% 3.24/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.24/0.99      theory(equality) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_901,plain,
% 3.24/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 3.24/0.99      inference(resolution,[status(thm)],[c_155,c_158]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_0,plain,
% 3.24/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.24/0.99      inference(cnf_transformation,[],[f22]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_1078,plain,
% 3.24/0.99      ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
% 3.24/0.99      | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 3.24/0.99      inference(resolution,[status(thm)],[c_901,c_0]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_3,plain,
% 3.24/0.99      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 3.24/0.99      inference(cnf_transformation,[],[f25]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_4,plain,
% 3.24/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 3.24/0.99      inference(cnf_transformation,[],[f19]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_87,plain,
% 3.24/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.24/0.99      | r1_xboole_0(X2,X1)
% 3.24/0.99      | X0 != X3
% 3.24/0.99      | k4_xboole_0(X3,k4_xboole_0(X3,X4)) != X2 ),
% 3.24/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_4]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_88,plain,
% 3.24/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.24/0.99      | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X1) ),
% 3.24/0.99      inference(unflattening,[status(thm)],[c_87]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_2090,plain,
% 3.24/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.24/0.99      | r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X0)),X1) ),
% 3.24/0.99      inference(resolution,[status(thm)],[c_1078,c_88]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_156,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_915,plain,
% 3.24/0.99      ( X0 != X1 | X1 = X0 ),
% 3.24/0.99      inference(resolution,[status(thm)],[c_156,c_155]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_2,plain,
% 3.24/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.24/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.24/0.99      inference(cnf_transformation,[],[f24]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_923,plain,
% 3.24/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.24/0.99      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 3.24/0.99      inference(resolution,[status(thm)],[c_915,c_2]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_909,plain,
% 3.24/0.99      ( X0 != k4_xboole_0(X1,k4_xboole_0(X1,X2))
% 3.24/0.99      | k4_xboole_0(X2,k4_xboole_0(X2,X1)) = X0 ),
% 3.24/0.99      inference(resolution,[status(thm)],[c_156,c_0]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_1201,plain,
% 3.24/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.24/0.99      | k4_xboole_0(X1,k4_xboole_0(X1,X0)) = k1_xboole_0 ),
% 3.24/0.99      inference(resolution,[status(thm)],[c_923,c_909]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_1,plain,
% 3.24/0.99      ( r1_xboole_0(X0,X1)
% 3.24/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 3.24/0.99      inference(cnf_transformation,[],[f23]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_1209,plain,
% 3.24/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.24/0.99      inference(resolution,[status(thm)],[c_1201,c_1]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_2317,plain,
% 3.24/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.24/0.99      | r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0))) ),
% 3.24/0.99      inference(resolution,[status(thm)],[c_2090,c_1209]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_5,negated_conjecture,
% 3.24/0.99      ( ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
% 3.24/0.99      inference(cnf_transformation,[],[f26]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_2319,plain,
% 3.24/0.99      ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
% 3.24/0.99      inference(resolution,[status(thm)],[c_2090,c_5]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_2467,plain,
% 3.24/0.99      ( ~ r1_xboole_0(sK1,sK0) ),
% 3.24/0.99      inference(resolution,[status(thm)],[c_2317,c_2319]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_6,negated_conjecture,
% 3.24/0.99      ( r1_xboole_0(sK0,sK1) ),
% 3.24/0.99      inference(cnf_transformation,[],[f20]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_306,plain,
% 3.24/0.99      ( r1_xboole_0(sK0,sK1) = iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_308,plain,
% 3.24/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 3.24/0.99      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_437,plain,
% 3.24/0.99      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 3.24/0.99      inference(superposition,[status(thm)],[c_306,c_308]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_309,plain,
% 3.24/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 3.24/0.99      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.24/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_496,plain,
% 3.24/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 3.24/0.99      | r1_xboole_0(X1,X0) = iProver_top ),
% 3.24/0.99      inference(superposition,[status(thm)],[c_0,c_309]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_650,plain,
% 3.24/0.99      ( r1_xboole_0(sK1,sK0) = iProver_top ),
% 3.24/0.99      inference(superposition,[status(thm)],[c_437,c_496]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(c_664,plain,
% 3.24/0.99      ( r1_xboole_0(sK1,sK0) ),
% 3.24/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_650]) ).
% 3.24/0.99  
% 3.24/0.99  cnf(contradiction,plain,
% 3.24/0.99      ( $false ),
% 3.24/0.99      inference(minisat,[status(thm)],[c_2467,c_664]) ).
% 3.24/0.99  
% 3.24/0.99  
% 3.24/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.24/0.99  
% 3.24/0.99  ------                               Statistics
% 3.24/0.99  
% 3.24/0.99  ------ Selected
% 3.24/0.99  
% 3.24/0.99  total_time:                             0.105
% 3.24/0.99  
%------------------------------------------------------------------------------
