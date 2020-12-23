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
% DateTime   : Thu Dec  3 11:38:22 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 127 expanded)
%              Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :   11 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :  107 ( 194 expanded)
%              Number of equality atoms :   79 ( 166 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f37,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f36])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k2_enumset1(X0,X0,X0,X0)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f21,f37,f37])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f24,f37])).

fof(f49,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f23,f21])).

fof(f39,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X2)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X2)),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X0,k3_xboole_0(X0,X2))))) ),
    inference(definition_unfolding,[],[f22,f35,f21,f21,f21,f35])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( X0 != X1
     => k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) = k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( X0 != X1
       => k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) = k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) != k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) != k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1))
        & X0 != X1 )
   => ( k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK1)) != k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK1)),k1_tarski(sK2))
      & sK1 != sK2 ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK1)) != k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK1)),k1_tarski(sK2))
    & sK1 != sK2 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f12,f18])).

fof(f34,plain,(
    k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK1)) != k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK1)),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,(
    k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2)))))) != k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK3))),k3_xboole_0(k5_xboole_0(sK3,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK3))),k2_enumset1(sK2,sK2,sK2,sK2))) ),
    inference(definition_unfolding,[],[f34,f35,f21,f37,f37,f21,f35,f37,f37])).

fof(f33,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_390,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k2_enumset1(X0,X0,X0,X0)
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_391,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_685,plain,
    ( X0 = X1
    | k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(X1,X1,X1,X1) ),
    inference(superposition,[status(thm)],[c_390,c_391])).

cnf(c_1,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))),X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1463,plain,
    ( X0 = X1
    | k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X2))),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X2))),k2_enumset1(X1,X1,X1,X1))) = k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))),k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k5_xboole_0(X2,k3_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)))))) ),
    inference(superposition,[status(thm)],[c_685,c_1])).

cnf(c_8,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2)))))) != k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK3))),k3_xboole_0(k5_xboole_0(sK3,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK3))),k2_enumset1(sK2,sK2,sK2,sK2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3104,plain,
    ( sK1 = sK2 ),
    inference(superposition,[status(thm)],[c_1463,c_8])).

cnf(c_9,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f33])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3104,c_9])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:39:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.18/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.00  
% 3.18/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.18/1.00  
% 3.18/1.00  ------  iProver source info
% 3.18/1.00  
% 3.18/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.18/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.18/1.00  git: non_committed_changes: false
% 3.18/1.00  git: last_make_outside_of_git: false
% 3.18/1.00  
% 3.18/1.00  ------ 
% 3.18/1.00  ------ Parsing...
% 3.18/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.18/1.00  ------ Proving...
% 3.18/1.00  ------ Problem Properties 
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  clauses                                 10
% 3.18/1.00  conjectures                             2
% 3.18/1.00  EPR                                     1
% 3.18/1.00  Horn                                    8
% 3.18/1.00  unary                                   5
% 3.18/1.00  binary                                  3
% 3.18/1.00  lits                                    17
% 3.18/1.00  lits eq                                 11
% 3.18/1.00  fd_pure                                 0
% 3.18/1.00  fd_pseudo                               0
% 3.18/1.00  fd_cond                                 0
% 3.18/1.00  fd_pseudo_cond                          2
% 3.18/1.00  AC symbols                              0
% 3.18/1.00  
% 3.18/1.00  ------ Input Options Time Limit: Unbounded
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  ------ 
% 3.18/1.00  Current options:
% 3.18/1.00  ------ 
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  ------ Proving...
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  % SZS status Theorem for theBenchmark.p
% 3.18/1.00  
% 3.18/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.18/1.00  
% 3.18/1.00  fof(f9,axiom,(
% 3.18/1.00    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) <=> ~r2_hidden(X0,X1))),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f17,plain,(
% 3.18/1.00    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)))),
% 3.18/1.00    inference(nnf_transformation,[],[f9])).
% 3.18/1.00  
% 3.18/1.00  fof(f32,plain,(
% 3.18/1.00    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r2_hidden(X0,X1)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f17])).
% 3.18/1.00  
% 3.18/1.00  fof(f2,axiom,(
% 3.18/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f21,plain,(
% 3.18/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.18/1.00    inference(cnf_transformation,[],[f2])).
% 3.18/1.00  
% 3.18/1.00  fof(f6,axiom,(
% 3.18/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f28,plain,(
% 3.18/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f6])).
% 3.18/1.00  
% 3.18/1.00  fof(f7,axiom,(
% 3.18/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f29,plain,(
% 3.18/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f7])).
% 3.18/1.00  
% 3.18/1.00  fof(f8,axiom,(
% 3.18/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f30,plain,(
% 3.18/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f8])).
% 3.18/1.00  
% 3.18/1.00  fof(f36,plain,(
% 3.18/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.18/1.00    inference(definition_unfolding,[],[f29,f30])).
% 3.18/1.00  
% 3.18/1.00  fof(f37,plain,(
% 3.18/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.18/1.00    inference(definition_unfolding,[],[f28,f36])).
% 3.18/1.00  
% 3.18/1.00  fof(f44,plain,(
% 3.18/1.00    ( ! [X0,X1] : (k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k2_enumset1(X0,X0,X0,X0) | r2_hidden(X0,X1)) )),
% 3.18/1.00    inference(definition_unfolding,[],[f32,f21,f37,f37])).
% 3.18/1.00  
% 3.18/1.00  fof(f5,axiom,(
% 3.18/1.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f13,plain,(
% 3.18/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.18/1.00    inference(nnf_transformation,[],[f5])).
% 3.18/1.00  
% 3.18/1.00  fof(f14,plain,(
% 3.18/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.18/1.00    inference(rectify,[],[f13])).
% 3.18/1.00  
% 3.18/1.00  fof(f15,plain,(
% 3.18/1.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 3.18/1.00    introduced(choice_axiom,[])).
% 3.18/1.00  
% 3.18/1.00  fof(f16,plain,(
% 3.18/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.18/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).
% 3.18/1.00  
% 3.18/1.00  fof(f24,plain,(
% 3.18/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.18/1.00    inference(cnf_transformation,[],[f16])).
% 3.18/1.00  
% 3.18/1.00  fof(f43,plain,(
% 3.18/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 3.18/1.00    inference(definition_unfolding,[],[f24,f37])).
% 3.18/1.00  
% 3.18/1.00  fof(f49,plain,(
% 3.18/1.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 3.18/1.00    inference(equality_resolution,[],[f43])).
% 3.18/1.00  
% 3.18/1.00  fof(f3,axiom,(
% 3.18/1.00    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f22,plain,(
% 3.18/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f3])).
% 3.18/1.00  
% 3.18/1.00  fof(f4,axiom,(
% 3.18/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f23,plain,(
% 3.18/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.18/1.00    inference(cnf_transformation,[],[f4])).
% 3.18/1.00  
% 3.18/1.00  fof(f35,plain,(
% 3.18/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 3.18/1.00    inference(definition_unfolding,[],[f23,f21])).
% 3.18/1.00  
% 3.18/1.00  fof(f39,plain,(
% 3.18/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X2)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X2)),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X0,k3_xboole_0(X0,X2)))))) )),
% 3.18/1.00    inference(definition_unfolding,[],[f22,f35,f21,f21,f21,f35])).
% 3.18/1.00  
% 3.18/1.00  fof(f10,conjecture,(
% 3.18/1.00    ! [X0,X1,X2] : (X0 != X1 => k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) = k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)))),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f11,negated_conjecture,(
% 3.18/1.00    ~! [X0,X1,X2] : (X0 != X1 => k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) = k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)))),
% 3.18/1.00    inference(negated_conjecture,[],[f10])).
% 3.18/1.00  
% 3.18/1.00  fof(f12,plain,(
% 3.18/1.00    ? [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) != k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) & X0 != X1)),
% 3.18/1.00    inference(ennf_transformation,[],[f11])).
% 3.18/1.00  
% 3.18/1.00  fof(f18,plain,(
% 3.18/1.00    ? [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) != k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) & X0 != X1) => (k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK1)) != k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK1)),k1_tarski(sK2)) & sK1 != sK2)),
% 3.18/1.00    introduced(choice_axiom,[])).
% 3.18/1.00  
% 3.18/1.00  fof(f19,plain,(
% 3.18/1.00    k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK1)) != k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK1)),k1_tarski(sK2)) & sK1 != sK2),
% 3.18/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f12,f18])).
% 3.18/1.00  
% 3.18/1.00  fof(f34,plain,(
% 3.18/1.00    k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK1)) != k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK1)),k1_tarski(sK2))),
% 3.18/1.00    inference(cnf_transformation,[],[f19])).
% 3.18/1.00  
% 3.18/1.00  fof(f46,plain,(
% 3.18/1.00    k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2)))))) != k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK3))),k3_xboole_0(k5_xboole_0(sK3,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK3))),k2_enumset1(sK2,sK2,sK2,sK2)))),
% 3.18/1.00    inference(definition_unfolding,[],[f34,f35,f21,f37,f37,f21,f35,f37,f37])).
% 3.18/1.00  
% 3.18/1.00  fof(f33,plain,(
% 3.18/1.00    sK1 != sK2),
% 3.18/1.00    inference(cnf_transformation,[],[f19])).
% 3.18/1.00  
% 3.18/1.00  cnf(c_6,plain,
% 3.18/1.00      ( r2_hidden(X0,X1)
% 3.18/1.00      | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k2_enumset1(X0,X0,X0,X0) ),
% 3.18/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_390,plain,
% 3.18/1.00      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k2_enumset1(X0,X0,X0,X0)
% 3.18/1.00      | r2_hidden(X0,X1) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_5,plain,
% 3.18/1.00      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 3.18/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_391,plain,
% 3.18/1.00      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_685,plain,
% 3.18/1.00      ( X0 = X1
% 3.18/1.00      | k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(X1,X1,X1,X1) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_390,c_391]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1,plain,
% 3.18/1.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))),X1)) ),
% 3.18/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1463,plain,
% 3.18/1.00      ( X0 = X1
% 3.18/1.00      | k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X2))),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X2))),k2_enumset1(X1,X1,X1,X1))) = k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))),k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k5_xboole_0(X2,k3_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)))))) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_685,c_1]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_8,negated_conjecture,
% 3.18/1.00      ( k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k5_xboole_0(sK3,k3_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2)))))) != k5_xboole_0(k5_xboole_0(sK3,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK3))),k3_xboole_0(k5_xboole_0(sK3,k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK3))),k2_enumset1(sK2,sK2,sK2,sK2))) ),
% 3.18/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3104,plain,
% 3.18/1.00      ( sK1 = sK2 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1463,c_8]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_9,negated_conjecture,
% 3.18/1.00      ( sK1 != sK2 ),
% 3.18/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(contradiction,plain,
% 3.18/1.00      ( $false ),
% 3.18/1.00      inference(minisat,[status(thm)],[c_3104,c_9]) ).
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.18/1.00  
% 3.18/1.00  ------                               Statistics
% 3.18/1.00  
% 3.18/1.00  ------ Selected
% 3.18/1.00  
% 3.18/1.00  total_time:                             0.213
% 3.18/1.00  
%------------------------------------------------------------------------------
