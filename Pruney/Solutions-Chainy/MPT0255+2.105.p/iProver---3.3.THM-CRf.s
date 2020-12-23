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
% DateTime   : Thu Dec  3 11:34:33 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :   49 (  55 expanded)
%              Number of clauses        :   16 (  18 expanded)
%              Number of leaves         :   10 (  12 expanded)
%              Depth                    :   11
%              Number of atoms          :  148 ( 154 expanded)
%              Number of equality atoms :   92 (  95 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f17])).

fof(f23,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,
    ( ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)
   => k1_xboole_0 = k2_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f34])).

fof(f61,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f69,plain,(
    k1_xboole_0 = k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)) ),
    inference(definition_unfolding,[],[f61,f60])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_xboole_0(X0,X1)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k3_tarski(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f43,f60])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f29])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f47])).

fof(f75,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f74])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f25])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_8,plain,
    ( k3_tarski(k2_tarski(X0,X1)) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_8748,plain,
    ( k2_tarski(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_21,c_8])).

cnf(c_15,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_8690,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8755,plain,
    ( r2_hidden(sK2,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8748,c_8690])).

cnf(c_10,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_8691,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_8693,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_8921,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8691,c_8693])).

cnf(c_3,negated_conjecture,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_8692,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10302,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8921,c_8692])).

cnf(c_10575,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10302,c_8691])).

cnf(c_10579,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_8755,c_10575])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:15:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.67/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/0.98  
% 3.67/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.67/0.98  
% 3.67/0.98  ------  iProver source info
% 3.67/0.98  
% 3.67/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.67/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.67/0.98  git: non_committed_changes: false
% 3.67/0.98  git: last_make_outside_of_git: false
% 3.67/0.98  
% 3.67/0.98  ------ 
% 3.67/0.98  ------ Parsing...
% 3.67/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/0.98  ------ Proving...
% 3.67/0.98  ------ Problem Properties 
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  clauses                                 21
% 3.67/0.98  conjectures                             2
% 3.67/0.98  EPR                                     4
% 3.67/0.98  Horn                                    18
% 3.67/0.98  unary                                   10
% 3.67/0.98  binary                                  6
% 3.67/0.98  lits                                    38
% 3.67/0.98  lits eq                                 19
% 3.67/0.98  fd_pure                                 0
% 3.67/0.98  fd_pseudo                               0
% 3.67/0.98  fd_cond                                 1
% 3.67/0.98  fd_pseudo_cond                          4
% 3.67/0.98  AC symbols                              0
% 3.67/0.98  
% 3.67/0.98  ------ Input Options Time Limit: Unbounded
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing...
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.67/0.98  Current options:
% 3.67/0.98  ------ 
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ Proving...
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing...
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/0.98  
% 3.67/0.98  ------ Proving...
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/0.98  
% 3.67/0.98  ------ Proving...
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/0.98  
% 3.67/0.98  ------ Proving...
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/0.98  
% 3.67/0.98  ------ Proving...
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/0.98  
% 3.67/0.98  ------ Proving...
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/0.98  
% 3.67/0.98  ------ Proving...
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/0.98  
% 3.67/0.98  ------ Proving...
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/0.98  
% 3.67/0.98  ------ Proving...
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/0.98  
% 3.67/0.98  ------ Proving...
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/0.98  
% 3.67/0.98  ------ Proving...
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.67/0.98  
% 3.67/0.98  ------ Proving...
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  % SZS status Theorem for theBenchmark.p
% 3.67/0.98  
% 3.67/0.98   Resolution empty clause
% 3.67/0.98  
% 3.67/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.67/0.98  
% 3.67/0.98  fof(f17,conjecture,(
% 3.67/0.98    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 3.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f18,negated_conjecture,(
% 3.67/0.98    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 3.67/0.98    inference(negated_conjecture,[],[f17])).
% 3.67/0.98  
% 3.67/0.98  fof(f23,plain,(
% 3.67/0.98    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 3.67/0.98    inference(ennf_transformation,[],[f18])).
% 3.67/0.98  
% 3.67/0.98  fof(f34,plain,(
% 3.67/0.98    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) => k1_xboole_0 = k2_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 3.67/0.98    introduced(choice_axiom,[])).
% 3.67/0.98  
% 3.67/0.98  fof(f35,plain,(
% 3.67/0.98    k1_xboole_0 = k2_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 3.67/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f34])).
% 3.67/0.98  
% 3.67/0.98  fof(f61,plain,(
% 3.67/0.98    k1_xboole_0 = k2_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 3.67/0.98    inference(cnf_transformation,[],[f35])).
% 3.67/0.98  
% 3.67/0.98  fof(f16,axiom,(
% 3.67/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f60,plain,(
% 3.67/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.67/0.98    inference(cnf_transformation,[],[f16])).
% 3.67/0.98  
% 3.67/0.98  fof(f69,plain,(
% 3.67/0.98    k1_xboole_0 = k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4))),
% 3.67/0.98    inference(definition_unfolding,[],[f61,f60])).
% 3.67/0.98  
% 3.67/0.98  fof(f4,axiom,(
% 3.67/0.98    ! [X0,X1] : (k1_xboole_0 = k2_xboole_0(X0,X1) => k1_xboole_0 = X0)),
% 3.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f21,plain,(
% 3.67/0.98    ! [X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_xboole_0(X0,X1))),
% 3.67/0.98    inference(ennf_transformation,[],[f4])).
% 3.67/0.98  
% 3.67/0.98  fof(f43,plain,(
% 3.67/0.98    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_xboole_0(X0,X1)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f21])).
% 3.67/0.98  
% 3.67/0.98  fof(f65,plain,(
% 3.67/0.98    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 != k3_tarski(k2_tarski(X0,X1))) )),
% 3.67/0.98    inference(definition_unfolding,[],[f43,f60])).
% 3.67/0.98  
% 3.67/0.98  fof(f7,axiom,(
% 3.67/0.98    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f29,plain,(
% 3.67/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.67/0.98    inference(nnf_transformation,[],[f7])).
% 3.67/0.98  
% 3.67/0.98  fof(f30,plain,(
% 3.67/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.67/0.98    inference(flattening,[],[f29])).
% 3.67/0.98  
% 3.67/0.98  fof(f31,plain,(
% 3.67/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.67/0.98    inference(rectify,[],[f30])).
% 3.67/0.98  
% 3.67/0.98  fof(f32,plain,(
% 3.67/0.98    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.67/0.98    introduced(choice_axiom,[])).
% 3.67/0.98  
% 3.67/0.98  fof(f33,plain,(
% 3.67/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.67/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 3.67/0.98  
% 3.67/0.98  fof(f47,plain,(
% 3.67/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.67/0.98    inference(cnf_transformation,[],[f33])).
% 3.67/0.98  
% 3.67/0.98  fof(f74,plain,(
% 3.67/0.98    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 3.67/0.98    inference(equality_resolution,[],[f47])).
% 3.67/0.98  
% 3.67/0.98  fof(f75,plain,(
% 3.67/0.98    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 3.67/0.98    inference(equality_resolution,[],[f74])).
% 3.67/0.98  
% 3.67/0.98  fof(f6,axiom,(
% 3.67/0.98    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f45,plain,(
% 3.67/0.98    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f6])).
% 3.67/0.98  
% 3.67/0.98  fof(f1,axiom,(
% 3.67/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f24,plain,(
% 3.67/0.98    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.67/0.98    inference(nnf_transformation,[],[f1])).
% 3.67/0.98  
% 3.67/0.98  fof(f36,plain,(
% 3.67/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.67/0.98    inference(cnf_transformation,[],[f24])).
% 3.67/0.98  
% 3.67/0.98  fof(f2,axiom,(
% 3.67/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.67/0.98  
% 3.67/0.98  fof(f19,plain,(
% 3.67/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.67/0.98    inference(rectify,[],[f2])).
% 3.67/0.98  
% 3.67/0.98  fof(f20,plain,(
% 3.67/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.67/0.98    inference(ennf_transformation,[],[f19])).
% 3.67/0.98  
% 3.67/0.98  fof(f25,plain,(
% 3.67/0.98    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 3.67/0.98    introduced(choice_axiom,[])).
% 3.67/0.98  
% 3.67/0.98  fof(f26,plain,(
% 3.67/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.67/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f25])).
% 3.67/0.98  
% 3.67/0.98  fof(f39,plain,(
% 3.67/0.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.67/0.98    inference(cnf_transformation,[],[f26])).
% 3.67/0.98  
% 3.67/0.98  cnf(c_21,negated_conjecture,
% 3.67/0.98      ( k1_xboole_0 = k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)) ),
% 3.67/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_8,plain,
% 3.67/0.98      ( k3_tarski(k2_tarski(X0,X1)) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 3.67/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_8748,plain,
% 3.67/0.98      ( k2_tarski(sK2,sK3) = k1_xboole_0 ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_21,c_8]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_15,plain,
% 3.67/0.98      ( r2_hidden(X0,k2_tarski(X0,X1)) ),
% 3.67/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_8690,plain,
% 3.67/0.98      ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_8755,plain,
% 3.67/0.98      ( r2_hidden(sK2,k1_xboole_0) = iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_8748,c_8690]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_10,plain,
% 3.67/0.98      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.67/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_8691,plain,
% 3.67/0.98      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_2,plain,
% 3.67/0.98      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.67/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_8693,plain,
% 3.67/0.98      ( k3_xboole_0(X0,X1) = k1_xboole_0 | r1_xboole_0(X0,X1) != iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_8921,plain,
% 3.67/0.98      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_8691,c_8693]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_3,negated_conjecture,
% 3.67/0.98      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 3.67/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_8692,plain,
% 3.67/0.98      ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
% 3.67/0.98      | r1_xboole_0(X1,X2) != iProver_top ),
% 3.67/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_10302,plain,
% 3.67/0.98      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.67/0.98      | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_8921,c_8692]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_10575,plain,
% 3.67/0.98      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.67/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_10302,c_8691]) ).
% 3.67/0.98  
% 3.67/0.98  cnf(c_10579,plain,
% 3.67/0.98      ( $false ),
% 3.67/0.98      inference(superposition,[status(thm)],[c_8755,c_10575]) ).
% 3.67/0.98  
% 3.67/0.98  
% 3.67/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.67/0.98  
% 3.67/0.98  ------                               Statistics
% 3.67/0.98  
% 3.67/0.98  ------ Selected
% 3.67/0.98  
% 3.67/0.98  total_time:                             0.254
% 3.67/0.98  
%------------------------------------------------------------------------------
