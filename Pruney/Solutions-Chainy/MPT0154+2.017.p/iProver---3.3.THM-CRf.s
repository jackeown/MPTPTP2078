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
% DateTime   : Thu Dec  3 11:26:54 EST 2020

% Result     : Theorem 7.68s
% Output     : CNFRefutation 7.68s
% Verified   : 
% Statistics : Number of formulae       :   58 (  87 expanded)
%              Number of clauses        :   18 (  19 expanded)
%              Number of leaves         :   15 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  161 ( 201 expanded)
%              Number of equality atoms :   49 (  73 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    8 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f38,f35])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f37,f43])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f19])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f17])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f43])).

fof(f11,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(negated_conjecture,[],[f11])).

fof(f16,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)
   => k2_tarski(sK2,sK3) != k1_enumset1(sK2,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    k2_tarski(sK2,sK3) != k1_enumset1(sK2,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f24])).

fof(f42,plain,(
    k2_tarski(sK2,sK3) != k1_enumset1(sK2,sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f39,f43])).

fof(f45,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k1_tarski(X0)))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f43,f44])).

fof(f49,plain,(
    k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))) != k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK2)))) ),
    inference(definition_unfolding,[],[f42,f44,f45])).

cnf(c_102,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_11,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_12413,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X1)))))
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_102,c_11])).

cnf(c_97,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_13291,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) ),
    inference(resolution,[status(thm)],[c_12413,c_97])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_13541,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(resolution,[status(thm)],[c_13291,c_8])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_13909,plain,
    ( ~ r2_hidden(sK0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))),X1)
    | r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(resolution,[status(thm)],[c_13541,c_2])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_15019,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(resolution,[status(thm)],[c_13909,c_3])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_98,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_11910,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_98,c_97])).

cnf(c_12549,plain,
    ( ~ r1_tarski(X0,X1)
    | X1 = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(resolution,[status(thm)],[c_10,c_11910])).

cnf(c_12,negated_conjecture,
    ( k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))) != k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK2)))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_12706,plain,
    ( ~ r1_tarski(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2))))) ),
    inference(resolution,[status(thm)],[c_12549,c_12])).

cnf(c_15662,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_15019,c_12706])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:27:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.68/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.68/1.49  
% 7.68/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.68/1.49  
% 7.68/1.49  ------  iProver source info
% 7.68/1.49  
% 7.68/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.68/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.68/1.49  git: non_committed_changes: false
% 7.68/1.49  git: last_make_outside_of_git: false
% 7.68/1.49  
% 7.68/1.49  ------ 
% 7.68/1.49  ------ Parsing...
% 7.68/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.68/1.49  
% 7.68/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.68/1.49  
% 7.68/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.68/1.49  
% 7.68/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.68/1.49  ------ Proving...
% 7.68/1.49  ------ Problem Properties 
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  clauses                                 13
% 7.68/1.49  conjectures                             1
% 7.68/1.49  EPR                                     0
% 7.68/1.49  Horn                                    10
% 7.68/1.49  unary                                   4
% 7.68/1.49  binary                                  5
% 7.68/1.49  lits                                    27
% 7.68/1.49  lits eq                                 8
% 7.68/1.49  fd_pure                                 0
% 7.68/1.49  fd_pseudo                               0
% 7.68/1.49  fd_cond                                 0
% 7.68/1.49  fd_pseudo_cond                          3
% 7.68/1.49  AC symbols                              0
% 7.68/1.49  
% 7.68/1.49  ------ Input Options Time Limit: Unbounded
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  ------ Preprocessing...
% 7.68/1.49  
% 7.68/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 7.68/1.49  Current options:
% 7.68/1.49  ------ 
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  ------ Proving...
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  ------ Preprocessing...
% 7.68/1.49  
% 7.68/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.68/1.49  
% 7.68/1.49  ------ Proving...
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.68/1.49  
% 7.68/1.49  ------ Proving...
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.68/1.49  
% 7.68/1.49  ------ Proving...
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.68/1.49  
% 7.68/1.49  ------ Proving...
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.68/1.49  
% 7.68/1.49  ------ Proving...
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.68/1.49  
% 7.68/1.49  ------ Proving...
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.68/1.49  
% 7.68/1.49  ------ Proving...
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.68/1.49  
% 7.68/1.49  ------ Proving...
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.68/1.49  
% 7.68/1.49  ------ Proving...
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.68/1.49  
% 7.68/1.49  ------ Proving...
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  % SZS status Theorem for theBenchmark.p
% 7.68/1.49  
% 7.68/1.49   Resolution empty clause
% 7.68/1.49  
% 7.68/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.68/1.49  
% 7.68/1.49  fof(f6,axiom,(
% 7.68/1.49    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 7.68/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f37,plain,(
% 7.68/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 7.68/1.49    inference(cnf_transformation,[],[f6])).
% 7.68/1.49  
% 7.68/1.49  fof(f7,axiom,(
% 7.68/1.49    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.68/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f38,plain,(
% 7.68/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.68/1.49    inference(cnf_transformation,[],[f7])).
% 7.68/1.49  
% 7.68/1.49  fof(f4,axiom,(
% 7.68/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.68/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f35,plain,(
% 7.68/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.68/1.49    inference(cnf_transformation,[],[f4])).
% 7.68/1.49  
% 7.68/1.49  fof(f43,plain,(
% 7.68/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 7.68/1.49    inference(definition_unfolding,[],[f38,f35])).
% 7.68/1.49  
% 7.68/1.49  fof(f48,plain,(
% 7.68/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 7.68/1.49    inference(definition_unfolding,[],[f37,f43])).
% 7.68/1.49  
% 7.68/1.49  fof(f3,axiom,(
% 7.68/1.49    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.68/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f19,plain,(
% 7.68/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.68/1.49    inference(nnf_transformation,[],[f3])).
% 7.68/1.49  
% 7.68/1.49  fof(f20,plain,(
% 7.68/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.68/1.49    inference(flattening,[],[f19])).
% 7.68/1.49  
% 7.68/1.49  fof(f21,plain,(
% 7.68/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.68/1.49    inference(rectify,[],[f20])).
% 7.68/1.49  
% 7.68/1.49  fof(f22,plain,(
% 7.68/1.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.68/1.49    introduced(choice_axiom,[])).
% 7.68/1.49  
% 7.68/1.49  fof(f23,plain,(
% 7.68/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.68/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).
% 7.68/1.49  
% 7.68/1.49  fof(f30,plain,(
% 7.68/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 7.68/1.49    inference(cnf_transformation,[],[f23])).
% 7.68/1.49  
% 7.68/1.49  fof(f51,plain,(
% 7.68/1.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 7.68/1.49    inference(equality_resolution,[],[f30])).
% 7.68/1.49  
% 7.68/1.49  fof(f2,axiom,(
% 7.68/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.68/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f13,plain,(
% 7.68/1.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 7.68/1.49    inference(unused_predicate_definition_removal,[],[f2])).
% 7.68/1.49  
% 7.68/1.49  fof(f14,plain,(
% 7.68/1.49    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 7.68/1.49    inference(ennf_transformation,[],[f13])).
% 7.68/1.49  
% 7.68/1.49  fof(f17,plain,(
% 7.68/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.68/1.49    introduced(choice_axiom,[])).
% 7.68/1.49  
% 7.68/1.49  fof(f18,plain,(
% 7.68/1.49    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.68/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f17])).
% 7.68/1.49  
% 7.68/1.49  fof(f28,plain,(
% 7.68/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.68/1.49    inference(cnf_transformation,[],[f18])).
% 7.68/1.49  
% 7.68/1.49  fof(f27,plain,(
% 7.68/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.68/1.49    inference(cnf_transformation,[],[f18])).
% 7.68/1.49  
% 7.68/1.49  fof(f5,axiom,(
% 7.68/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.68/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f15,plain,(
% 7.68/1.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.68/1.49    inference(ennf_transformation,[],[f5])).
% 7.68/1.49  
% 7.68/1.49  fof(f36,plain,(
% 7.68/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.68/1.49    inference(cnf_transformation,[],[f15])).
% 7.68/1.49  
% 7.68/1.49  fof(f47,plain,(
% 7.68/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 | ~r1_tarski(X0,X1)) )),
% 7.68/1.49    inference(definition_unfolding,[],[f36,f43])).
% 7.68/1.49  
% 7.68/1.49  fof(f11,conjecture,(
% 7.68/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.68/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f12,negated_conjecture,(
% 7.68/1.49    ~! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.68/1.49    inference(negated_conjecture,[],[f11])).
% 7.68/1.49  
% 7.68/1.49  fof(f16,plain,(
% 7.68/1.49    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)),
% 7.68/1.49    inference(ennf_transformation,[],[f12])).
% 7.68/1.49  
% 7.68/1.49  fof(f24,plain,(
% 7.68/1.49    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) => k2_tarski(sK2,sK3) != k1_enumset1(sK2,sK2,sK3)),
% 7.68/1.49    introduced(choice_axiom,[])).
% 7.68/1.49  
% 7.68/1.49  fof(f25,plain,(
% 7.68/1.49    k2_tarski(sK2,sK3) != k1_enumset1(sK2,sK2,sK3)),
% 7.68/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f24])).
% 7.68/1.49  
% 7.68/1.49  fof(f42,plain,(
% 7.68/1.49    k2_tarski(sK2,sK3) != k1_enumset1(sK2,sK2,sK3)),
% 7.68/1.49    inference(cnf_transformation,[],[f25])).
% 7.68/1.49  
% 7.68/1.49  fof(f9,axiom,(
% 7.68/1.49    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)),
% 7.68/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f40,plain,(
% 7.68/1.49    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)) )),
% 7.68/1.49    inference(cnf_transformation,[],[f9])).
% 7.68/1.49  
% 7.68/1.49  fof(f8,axiom,(
% 7.68/1.49    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 7.68/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f39,plain,(
% 7.68/1.49    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 7.68/1.49    inference(cnf_transformation,[],[f8])).
% 7.68/1.49  
% 7.68/1.49  fof(f44,plain,(
% 7.68/1.49    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))) = k2_tarski(X0,X1)) )),
% 7.68/1.49    inference(definition_unfolding,[],[f39,f43])).
% 7.68/1.49  
% 7.68/1.49  fof(f45,plain,(
% 7.68/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k1_tarski(X0)))) = k1_enumset1(X0,X1,X2)) )),
% 7.68/1.49    inference(definition_unfolding,[],[f40,f43,f44])).
% 7.68/1.49  
% 7.68/1.49  fof(f49,plain,(
% 7.68/1.49    k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))) != k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK2))))),
% 7.68/1.49    inference(definition_unfolding,[],[f42,f44,f45])).
% 7.68/1.49  
% 7.68/1.49  cnf(c_102,plain,
% 7.68/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.68/1.49      theory(equality) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_11,plain,
% 7.68/1.49      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 7.68/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_12413,plain,
% 7.68/1.49      ( ~ r2_hidden(X0,X1)
% 7.68/1.49      | r2_hidden(X2,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X1)))))
% 7.68/1.49      | X2 != X0 ),
% 7.68/1.49      inference(resolution,[status(thm)],[c_102,c_11]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_97,plain,( X0 = X0 ),theory(equality) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_13291,plain,
% 7.68/1.49      ( ~ r2_hidden(X0,X1)
% 7.68/1.49      | r2_hidden(X0,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) ),
% 7.68/1.49      inference(resolution,[status(thm)],[c_12413,c_97]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_8,plain,
% 7.68/1.49      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 7.68/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_13541,plain,
% 7.68/1.49      ( ~ r2_hidden(X0,X1)
% 7.68/1.49      | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
% 7.68/1.49      inference(resolution,[status(thm)],[c_13291,c_8]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_2,plain,
% 7.68/1.49      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.68/1.49      inference(cnf_transformation,[],[f28]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_13909,plain,
% 7.68/1.49      ( ~ r2_hidden(sK0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))),X1)
% 7.68/1.49      | r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
% 7.68/1.49      inference(resolution,[status(thm)],[c_13541,c_2]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_3,plain,
% 7.68/1.49      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.68/1.49      inference(cnf_transformation,[],[f27]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_15019,plain,
% 7.68/1.49      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
% 7.68/1.49      inference(resolution,[status(thm)],[c_13909,c_3]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_10,plain,
% 7.68/1.49      ( ~ r1_tarski(X0,X1)
% 7.68/1.49      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 ),
% 7.68/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_98,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_11910,plain,
% 7.68/1.49      ( X0 != X1 | X1 = X0 ),
% 7.68/1.49      inference(resolution,[status(thm)],[c_98,c_97]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_12549,plain,
% 7.68/1.49      ( ~ r1_tarski(X0,X1)
% 7.68/1.49      | X1 = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 7.68/1.49      inference(resolution,[status(thm)],[c_10,c_11910]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_12,negated_conjecture,
% 7.68/1.49      ( k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))) != k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))),k1_tarski(sK2)))) ),
% 7.68/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_12706,plain,
% 7.68/1.49      ( ~ r1_tarski(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),k1_tarski(sK2))))) ),
% 7.68/1.49      inference(resolution,[status(thm)],[c_12549,c_12]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_15662,plain,
% 7.68/1.49      ( $false ),
% 7.68/1.49      inference(backward_subsumption_resolution,
% 7.68/1.49                [status(thm)],
% 7.68/1.49                [c_15019,c_12706]) ).
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.68/1.49  
% 7.68/1.49  ------                               Statistics
% 7.68/1.49  
% 7.68/1.49  ------ Selected
% 7.68/1.49  
% 7.68/1.49  total_time:                             0.633
% 7.68/1.49  
%------------------------------------------------------------------------------
