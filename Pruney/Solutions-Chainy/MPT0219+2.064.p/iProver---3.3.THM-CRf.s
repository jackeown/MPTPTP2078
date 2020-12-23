%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:19 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   60 (  94 expanded)
%              Number of clauses        :   16 (  17 expanded)
%              Number of leaves         :   12 (  25 expanded)
%              Depth                    :   13
%              Number of atoms          :  220 ( 339 expanded)
%              Number of equality atoms :  163 ( 244 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f19,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK2 != sK3
      & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( sK2 != sK3
    & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f29])).

fof(f56,plain,(
    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f58,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f37,f32])).

fof(f12,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f78,plain,(
    k5_xboole_0(k2_tarski(sK2,sK2),k5_xboole_0(k2_tarski(sK3,sK3),k3_xboole_0(k2_tarski(sK3,sK3),k2_tarski(sK2,sK2)))) = k2_tarski(sK2,sK2) ),
    inference(definition_unfolding,[],[f56,f58,f52,f52,f52])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f20])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f40,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f50,f58])).

fof(f60,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f54,f59])).

fof(f70,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3 ) ),
    inference(definition_unfolding,[],[f40,f60])).

fof(f81,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X5,X2),k3_xboole_0(k2_tarski(X5,X2),k2_tarski(X0,X0)))) != X3 ) ),
    inference(equality_resolution,[],[f70])).

fof(f82,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X5,X2),k3_xboole_0(k2_tarski(X5,X2),k2_tarski(X0,X0))))) ),
    inference(equality_resolution,[],[f81])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f46,f52])).

fof(f88,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_tarski(X0,X0)) ) ),
    inference(equality_resolution,[],[f76])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f47,f52])).

fof(f86,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f75])).

fof(f87,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f86])).

fof(f57,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_20,negated_conjecture,
    ( k5_xboole_0(k2_tarski(sK2,sK2),k5_xboole_0(k2_tarski(sK3,sK3),k3_xboole_0(k2_tarski(sK3,sK3),k2_tarski(sK2,sK2)))) = k2_tarski(sK2,sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_11,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X0,X2),k3_xboole_0(k2_tarski(X0,X2),k2_tarski(X1,X1))))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_902,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X0,X2),k3_xboole_0(k2_tarski(X0,X2),k2_tarski(X1,X1))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4197,plain,
    ( r2_hidden(sK3,k2_tarski(sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_902])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_983,plain,
    ( ~ r2_hidden(sK3,k2_tarski(X0,X0))
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_984,plain,
    ( sK3 = X0
    | r2_hidden(sK3,k2_tarski(X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_983])).

cnf(c_986,plain,
    ( sK3 = sK2
    | r2_hidden(sK3,k2_tarski(sK2,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_984])).

cnf(c_690,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_951,plain,
    ( sK3 != X0
    | sK2 != X0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_690])).

cnf(c_952,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_951])).

cnf(c_16,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_26,plain,
    ( r2_hidden(sK2,k2_tarski(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_23,plain,
    ( ~ r2_hidden(sK2,k2_tarski(sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_19,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f57])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4197,c_986,c_952,c_26,c_23,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:15:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.29/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/0.99  
% 3.29/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.29/0.99  
% 3.29/0.99  ------  iProver source info
% 3.29/0.99  
% 3.29/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.29/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.29/0.99  git: non_committed_changes: false
% 3.29/0.99  git: last_make_outside_of_git: false
% 3.29/0.99  
% 3.29/0.99  ------ 
% 3.29/0.99  ------ Parsing...
% 3.29/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.29/0.99  
% 3.29/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.29/0.99  
% 3.29/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.29/0.99  
% 3.29/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.29/0.99  ------ Proving...
% 3.29/0.99  ------ Problem Properties 
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  clauses                                 21
% 3.29/0.99  conjectures                             2
% 3.29/0.99  EPR                                     1
% 3.29/0.99  Horn                                    18
% 3.29/0.99  unary                                   13
% 3.29/0.99  binary                                  1
% 3.29/0.99  lits                                    39
% 3.29/0.99  lits eq                                 27
% 3.29/0.99  fd_pure                                 0
% 3.29/0.99  fd_pseudo                               0
% 3.29/0.99  fd_cond                                 0
% 3.29/0.99  fd_pseudo_cond                          6
% 3.29/0.99  AC symbols                              0
% 3.29/0.99  
% 3.29/0.99  ------ Input Options Time Limit: Unbounded
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  ------ 
% 3.29/0.99  Current options:
% 3.29/0.99  ------ 
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  ------ Proving...
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  % SZS status Theorem for theBenchmark.p
% 3.29/0.99  
% 3.29/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.29/0.99  
% 3.29/0.99  fof(f16,conjecture,(
% 3.29/0.99    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f17,negated_conjecture,(
% 3.29/0.99    ~! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 3.29/0.99    inference(negated_conjecture,[],[f16])).
% 3.29/0.99  
% 3.29/0.99  fof(f19,plain,(
% 3.29/0.99    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 3.29/0.99    inference(ennf_transformation,[],[f17])).
% 3.29/0.99  
% 3.29/0.99  fof(f29,plain,(
% 3.29/0.99    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK2 != sK3 & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2))),
% 3.29/0.99    introduced(choice_axiom,[])).
% 3.29/0.99  
% 3.29/0.99  fof(f30,plain,(
% 3.29/0.99    sK2 != sK3 & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 3.29/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f29])).
% 3.29/0.99  
% 3.29/0.99  fof(f56,plain,(
% 3.29/0.99    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 3.29/0.99    inference(cnf_transformation,[],[f30])).
% 3.29/0.99  
% 3.29/0.99  fof(f7,axiom,(
% 3.29/0.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f37,plain,(
% 3.29/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f7])).
% 3.29/0.99  
% 3.29/0.99  fof(f2,axiom,(
% 3.29/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f32,plain,(
% 3.29/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.29/0.99    inference(cnf_transformation,[],[f2])).
% 3.29/0.99  
% 3.29/0.99  fof(f58,plain,(
% 3.29/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.29/0.99    inference(definition_unfolding,[],[f37,f32])).
% 3.29/0.99  
% 3.29/0.99  fof(f12,axiom,(
% 3.29/0.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f52,plain,(
% 3.29/0.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f12])).
% 3.29/0.99  
% 3.29/0.99  fof(f78,plain,(
% 3.29/0.99    k5_xboole_0(k2_tarski(sK2,sK2),k5_xboole_0(k2_tarski(sK3,sK3),k3_xboole_0(k2_tarski(sK3,sK3),k2_tarski(sK2,sK2)))) = k2_tarski(sK2,sK2)),
% 3.29/0.99    inference(definition_unfolding,[],[f56,f58,f52,f52,f52])).
% 3.29/0.99  
% 3.29/0.99  fof(f8,axiom,(
% 3.29/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f18,plain,(
% 3.29/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.29/0.99    inference(ennf_transformation,[],[f8])).
% 3.29/0.99  
% 3.29/0.99  fof(f20,plain,(
% 3.29/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.29/0.99    inference(nnf_transformation,[],[f18])).
% 3.29/0.99  
% 3.29/0.99  fof(f21,plain,(
% 3.29/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.29/0.99    inference(flattening,[],[f20])).
% 3.29/0.99  
% 3.29/0.99  fof(f22,plain,(
% 3.29/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.29/0.99    inference(rectify,[],[f21])).
% 3.29/0.99  
% 3.29/0.99  fof(f23,plain,(
% 3.29/0.99    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 3.29/0.99    introduced(choice_axiom,[])).
% 3.29/0.99  
% 3.29/0.99  fof(f24,plain,(
% 3.29/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.29/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 3.29/0.99  
% 3.29/0.99  fof(f40,plain,(
% 3.29/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.29/0.99    inference(cnf_transformation,[],[f24])).
% 3.29/0.99  
% 3.29/0.99  fof(f14,axiom,(
% 3.29/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f54,plain,(
% 3.29/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f14])).
% 3.29/0.99  
% 3.29/0.99  fof(f10,axiom,(
% 3.29/0.99    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f50,plain,(
% 3.29/0.99    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f10])).
% 3.29/0.99  
% 3.29/0.99  fof(f59,plain,(
% 3.29/0.99    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)))) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.29/0.99    inference(definition_unfolding,[],[f50,f58])).
% 3.29/0.99  
% 3.29/0.99  fof(f60,plain,(
% 3.29/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k1_enumset1(X0,X1,X2)) )),
% 3.29/0.99    inference(definition_unfolding,[],[f54,f59])).
% 3.29/0.99  
% 3.29/0.99  fof(f70,plain,(
% 3.29/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3) )),
% 3.29/0.99    inference(definition_unfolding,[],[f40,f60])).
% 3.29/0.99  
% 3.29/0.99  fof(f81,plain,(
% 3.29/0.99    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X5,X2),k3_xboole_0(k2_tarski(X5,X2),k2_tarski(X0,X0)))) != X3) )),
% 3.29/0.99    inference(equality_resolution,[],[f70])).
% 3.29/0.99  
% 3.29/0.99  fof(f82,plain,(
% 3.29/0.99    ( ! [X2,X0,X5] : (r2_hidden(X5,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X5,X2),k3_xboole_0(k2_tarski(X5,X2),k2_tarski(X0,X0)))))) )),
% 3.29/0.99    inference(equality_resolution,[],[f81])).
% 3.29/0.99  
% 3.29/0.99  fof(f9,axiom,(
% 3.29/0.99    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f25,plain,(
% 3.29/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.29/0.99    inference(nnf_transformation,[],[f9])).
% 3.29/0.99  
% 3.29/0.99  fof(f26,plain,(
% 3.29/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.29/0.99    inference(rectify,[],[f25])).
% 3.29/0.99  
% 3.29/0.99  fof(f27,plain,(
% 3.29/0.99    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 3.29/0.99    introduced(choice_axiom,[])).
% 3.29/0.99  
% 3.29/0.99  fof(f28,plain,(
% 3.29/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.29/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 3.29/0.99  
% 3.29/0.99  fof(f46,plain,(
% 3.29/0.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.29/0.99    inference(cnf_transformation,[],[f28])).
% 3.29/0.99  
% 3.29/0.99  fof(f76,plain,(
% 3.29/0.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 3.29/0.99    inference(definition_unfolding,[],[f46,f52])).
% 3.29/0.99  
% 3.29/0.99  fof(f88,plain,(
% 3.29/0.99    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_tarski(X0,X0))) )),
% 3.29/0.99    inference(equality_resolution,[],[f76])).
% 3.29/0.99  
% 3.29/0.99  fof(f47,plain,(
% 3.29/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.29/0.99    inference(cnf_transformation,[],[f28])).
% 3.29/0.99  
% 3.29/0.99  fof(f75,plain,(
% 3.29/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 3.29/0.99    inference(definition_unfolding,[],[f47,f52])).
% 3.29/0.99  
% 3.29/0.99  fof(f86,plain,(
% 3.29/0.99    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 3.29/0.99    inference(equality_resolution,[],[f75])).
% 3.29/0.99  
% 3.29/0.99  fof(f87,plain,(
% 3.29/0.99    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 3.29/0.99    inference(equality_resolution,[],[f86])).
% 3.29/0.99  
% 3.29/0.99  fof(f57,plain,(
% 3.29/0.99    sK2 != sK3),
% 3.29/0.99    inference(cnf_transformation,[],[f30])).
% 3.29/0.99  
% 3.29/0.99  cnf(c_20,negated_conjecture,
% 3.29/0.99      ( k5_xboole_0(k2_tarski(sK2,sK2),k5_xboole_0(k2_tarski(sK3,sK3),k3_xboole_0(k2_tarski(sK3,sK3),k2_tarski(sK2,sK2)))) = k2_tarski(sK2,sK2) ),
% 3.29/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_11,plain,
% 3.29/0.99      ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X0,X2),k3_xboole_0(k2_tarski(X0,X2),k2_tarski(X1,X1))))) ),
% 3.29/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_902,plain,
% 3.29/0.99      ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X0,X2),k3_xboole_0(k2_tarski(X0,X2),k2_tarski(X1,X1))))) = iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_4197,plain,
% 3.29/0.99      ( r2_hidden(sK3,k2_tarski(sK2,sK2)) = iProver_top ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_20,c_902]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_17,plain,
% 3.29/0.99      ( ~ r2_hidden(X0,k2_tarski(X1,X1)) | X0 = X1 ),
% 3.29/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_983,plain,
% 3.29/0.99      ( ~ r2_hidden(sK3,k2_tarski(X0,X0)) | sK3 = X0 ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_984,plain,
% 3.29/0.99      ( sK3 = X0 | r2_hidden(sK3,k2_tarski(X0,X0)) != iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_983]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_986,plain,
% 3.29/0.99      ( sK3 = sK2 | r2_hidden(sK3,k2_tarski(sK2,sK2)) != iProver_top ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_984]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_690,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_951,plain,
% 3.29/0.99      ( sK3 != X0 | sK2 != X0 | sK2 = sK3 ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_690]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_952,plain,
% 3.29/0.99      ( sK3 != sK2 | sK2 = sK3 | sK2 != sK2 ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_951]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_16,plain,
% 3.29/0.99      ( r2_hidden(X0,k2_tarski(X0,X0)) ),
% 3.29/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_26,plain,
% 3.29/0.99      ( r2_hidden(sK2,k2_tarski(sK2,sK2)) ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_23,plain,
% 3.29/0.99      ( ~ r2_hidden(sK2,k2_tarski(sK2,sK2)) | sK2 = sK2 ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_19,negated_conjecture,
% 3.29/0.99      ( sK2 != sK3 ),
% 3.29/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(contradiction,plain,
% 3.29/0.99      ( $false ),
% 3.29/0.99      inference(minisat,[status(thm)],[c_4197,c_986,c_952,c_26,c_23,c_19]) ).
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.29/0.99  
% 3.29/0.99  ------                               Statistics
% 3.29/0.99  
% 3.29/0.99  ------ Selected
% 3.29/0.99  
% 3.29/0.99  total_time:                             0.175
% 3.29/0.99  
%------------------------------------------------------------------------------
