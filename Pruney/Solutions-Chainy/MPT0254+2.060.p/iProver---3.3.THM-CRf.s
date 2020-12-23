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
% DateTime   : Thu Dec  3 11:33:56 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 109 expanded)
%              Number of clauses        :   14 (  16 expanded)
%              Number of leaves         :   13 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  202 ( 324 expanded)
%              Number of equality atoms :  106 ( 202 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f36,f45])).

fof(f60,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f53])).

fof(f61,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f60])).

fof(f10,conjecture,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,
    ( ? [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
   => k2_xboole_0(k1_tarski(sK2),sK3) = k1_xboole_0 ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    k2_xboole_0(k1_tarski(sK2),sK3) = k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f12,f23])).

fof(f44,plain,(
    k2_xboole_0(k1_tarski(sK2),sK3) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f43,f45])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f45])).

fof(f56,plain,(
    k1_xboole_0 = k3_tarski(k2_enumset1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),sK3)) ),
    inference(definition_unfolding,[],[f44,f46,f47])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f25,f46,f46])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) ),
    inference(definition_unfolding,[],[f33,f46])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f13])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

cnf(c_12,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2222,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k2_enumset1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),sK3)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_0,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2322,plain,
    ( k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK2,sK2,sK2,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_15,c_0])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2375,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK3),k2_enumset1(sK2,sK2,sK2,sK2)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2322,c_8])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_2376,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK3),k2_enumset1(sK2,sK2,sK2,sK2)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2375,c_7])).

cnf(c_5,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2224,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2387,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2376,c_2224])).

cnf(c_2416,plain,
    ( r2_hidden(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2222,c_2387])).

cnf(c_2459,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2222,c_2416])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:12:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 3.37/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.00  
% 3.37/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.37/1.00  
% 3.37/1.00  ------  iProver source info
% 3.37/1.00  
% 3.37/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.37/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.37/1.00  git: non_committed_changes: false
% 3.37/1.00  git: last_make_outside_of_git: false
% 3.37/1.00  
% 3.37/1.00  ------ 
% 3.37/1.00  ------ Parsing...
% 3.37/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.37/1.00  ------ Proving...
% 3.37/1.00  ------ Problem Properties 
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  clauses                                 16
% 3.37/1.00  conjectures                             2
% 3.37/1.00  EPR                                     0
% 3.37/1.00  Horn                                    10
% 3.37/1.00  unary                                   6
% 3.37/1.00  binary                                  2
% 3.37/1.00  lits                                    36
% 3.37/1.00  lits eq                                 16
% 3.37/1.00  fd_pure                                 0
% 3.37/1.00  fd_pseudo                               0
% 3.37/1.00  fd_cond                                 0
% 3.37/1.00  fd_pseudo_cond                          6
% 3.37/1.00  AC symbols                              0
% 3.37/1.00  
% 3.37/1.00  ------ Input Options Time Limit: Unbounded
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing...
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.37/1.00  Current options:
% 3.37/1.00  ------ 
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  ------ Proving...
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing...
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.37/1.00  
% 3.37/1.00  ------ Proving...
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.37/1.00  
% 3.37/1.00  ------ Proving...
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.37/1.00  
% 3.37/1.00  ------ Proving...
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.37/1.00  
% 3.37/1.00  ------ Proving...
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.37/1.00  
% 3.37/1.00  ------ Proving...
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.37/1.00  
% 3.37/1.00  ------ Proving...
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.37/1.00  
% 3.37/1.00  ------ Proving...
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.37/1.00  
% 3.37/1.00  ------ Proving...
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.37/1.00  
% 3.37/1.00  ------ Proving...
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.37/1.00  
% 3.37/1.00  ------ Proving...
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  % SZS status Theorem for theBenchmark.p
% 3.37/1.00  
% 3.37/1.00   Resolution empty clause
% 3.37/1.00  
% 3.37/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.37/1.00  
% 3.37/1.00  fof(f5,axiom,(
% 3.37/1.00    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.37/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f18,plain,(
% 3.37/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.37/1.00    inference(nnf_transformation,[],[f5])).
% 3.37/1.00  
% 3.37/1.00  fof(f19,plain,(
% 3.37/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.37/1.00    inference(flattening,[],[f18])).
% 3.37/1.00  
% 3.37/1.00  fof(f20,plain,(
% 3.37/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.37/1.00    inference(rectify,[],[f19])).
% 3.37/1.00  
% 3.37/1.00  fof(f21,plain,(
% 3.37/1.00    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.37/1.00    introduced(choice_axiom,[])).
% 3.37/1.00  
% 3.37/1.00  fof(f22,plain,(
% 3.37/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.37/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).
% 3.37/1.00  
% 3.37/1.00  fof(f36,plain,(
% 3.37/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.37/1.00    inference(cnf_transformation,[],[f22])).
% 3.37/1.00  
% 3.37/1.00  fof(f7,axiom,(
% 3.37/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.37/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f41,plain,(
% 3.37/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f7])).
% 3.37/1.00  
% 3.37/1.00  fof(f8,axiom,(
% 3.37/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.37/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f42,plain,(
% 3.37/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f8])).
% 3.37/1.00  
% 3.37/1.00  fof(f45,plain,(
% 3.37/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.37/1.00    inference(definition_unfolding,[],[f41,f42])).
% 3.37/1.00  
% 3.37/1.00  fof(f53,plain,(
% 3.37/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 3.37/1.00    inference(definition_unfolding,[],[f36,f45])).
% 3.37/1.00  
% 3.37/1.00  fof(f60,plain,(
% 3.37/1.00    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 3.37/1.00    inference(equality_resolution,[],[f53])).
% 3.37/1.00  
% 3.37/1.00  fof(f61,plain,(
% 3.37/1.00    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 3.37/1.00    inference(equality_resolution,[],[f60])).
% 3.37/1.00  
% 3.37/1.00  fof(f10,conjecture,(
% 3.37/1.00    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 3.37/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f11,negated_conjecture,(
% 3.37/1.00    ~! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 3.37/1.00    inference(negated_conjecture,[],[f10])).
% 3.37/1.00  
% 3.37/1.00  fof(f12,plain,(
% 3.37/1.00    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) = k1_xboole_0),
% 3.37/1.00    inference(ennf_transformation,[],[f11])).
% 3.37/1.00  
% 3.37/1.00  fof(f23,plain,(
% 3.37/1.00    ? [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 => k2_xboole_0(k1_tarski(sK2),sK3) = k1_xboole_0),
% 3.37/1.00    introduced(choice_axiom,[])).
% 3.37/1.00  
% 3.37/1.00  fof(f24,plain,(
% 3.37/1.00    k2_xboole_0(k1_tarski(sK2),sK3) = k1_xboole_0),
% 3.37/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f12,f23])).
% 3.37/1.00  
% 3.37/1.00  fof(f44,plain,(
% 3.37/1.00    k2_xboole_0(k1_tarski(sK2),sK3) = k1_xboole_0),
% 3.37/1.00    inference(cnf_transformation,[],[f24])).
% 3.37/1.00  
% 3.37/1.00  fof(f9,axiom,(
% 3.37/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.37/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f43,plain,(
% 3.37/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.37/1.00    inference(cnf_transformation,[],[f9])).
% 3.37/1.00  
% 3.37/1.00  fof(f46,plain,(
% 3.37/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 3.37/1.00    inference(definition_unfolding,[],[f43,f45])).
% 3.37/1.00  
% 3.37/1.00  fof(f6,axiom,(
% 3.37/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.37/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f40,plain,(
% 3.37/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f6])).
% 3.37/1.00  
% 3.37/1.00  fof(f47,plain,(
% 3.37/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.37/1.00    inference(definition_unfolding,[],[f40,f45])).
% 3.37/1.00  
% 3.37/1.00  fof(f56,plain,(
% 3.37/1.00    k1_xboole_0 = k3_tarski(k2_enumset1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),sK3))),
% 3.37/1.00    inference(definition_unfolding,[],[f44,f46,f47])).
% 3.37/1.00  
% 3.37/1.00  fof(f1,axiom,(
% 3.37/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.37/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f25,plain,(
% 3.37/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f1])).
% 3.37/1.00  
% 3.37/1.00  fof(f48,plain,(
% 3.37/1.00    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0))) )),
% 3.37/1.00    inference(definition_unfolding,[],[f25,f46,f46])).
% 3.37/1.00  
% 3.37/1.00  fof(f4,axiom,(
% 3.37/1.00    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.37/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f33,plain,(
% 3.37/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.37/1.00    inference(cnf_transformation,[],[f4])).
% 3.37/1.00  
% 3.37/1.00  fof(f49,plain,(
% 3.37/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))) )),
% 3.37/1.00    inference(definition_unfolding,[],[f33,f46])).
% 3.37/1.00  
% 3.37/1.00  fof(f3,axiom,(
% 3.37/1.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.37/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f32,plain,(
% 3.37/1.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.37/1.00    inference(cnf_transformation,[],[f3])).
% 3.37/1.00  
% 3.37/1.00  fof(f2,axiom,(
% 3.37/1.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.37/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/1.00  
% 3.37/1.00  fof(f13,plain,(
% 3.37/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.37/1.00    inference(nnf_transformation,[],[f2])).
% 3.37/1.00  
% 3.37/1.00  fof(f14,plain,(
% 3.37/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.37/1.00    inference(flattening,[],[f13])).
% 3.37/1.00  
% 3.37/1.00  fof(f15,plain,(
% 3.37/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.37/1.00    inference(rectify,[],[f14])).
% 3.37/1.00  
% 3.37/1.00  fof(f16,plain,(
% 3.37/1.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.37/1.00    introduced(choice_axiom,[])).
% 3.37/1.00  
% 3.37/1.00  fof(f17,plain,(
% 3.37/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.37/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 3.37/1.00  
% 3.37/1.00  fof(f27,plain,(
% 3.37/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.37/1.00    inference(cnf_transformation,[],[f17])).
% 3.37/1.00  
% 3.37/1.00  fof(f58,plain,(
% 3.37/1.00    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.37/1.00    inference(equality_resolution,[],[f27])).
% 3.37/1.00  
% 3.37/1.00  cnf(c_12,plain,
% 3.37/1.00      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
% 3.37/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2222,plain,
% 3.37/1.00      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_15,negated_conjecture,
% 3.37/1.00      ( k1_xboole_0 = k3_tarski(k2_enumset1(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2),sK3)) ),
% 3.37/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_0,plain,
% 3.37/1.00      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0)) ),
% 3.37/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2322,plain,
% 3.37/1.00      ( k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK2,sK2,sK2,sK2))) = k1_xboole_0 ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_15,c_0]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_8,plain,
% 3.37/1.00      ( k4_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 3.37/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2375,plain,
% 3.37/1.00      ( k4_xboole_0(k4_xboole_0(X0,sK3),k2_enumset1(sK2,sK2,sK2,sK2)) = k4_xboole_0(X0,k1_xboole_0) ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_2322,c_8]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_7,plain,
% 3.37/1.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.37/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2376,plain,
% 3.37/1.00      ( k4_xboole_0(k4_xboole_0(X0,sK3),k2_enumset1(sK2,sK2,sK2,sK2)) = X0 ),
% 3.37/1.00      inference(light_normalisation,[status(thm)],[c_2375,c_7]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_5,negated_conjecture,
% 3.37/1.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 3.37/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2224,plain,
% 3.37/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.37/1.00      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 3.37/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2387,plain,
% 3.37/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.37/1.00      | r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_2376,c_2224]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2416,plain,
% 3.37/1.00      ( r2_hidden(sK2,X0) != iProver_top ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_2222,c_2387]) ).
% 3.37/1.00  
% 3.37/1.00  cnf(c_2459,plain,
% 3.37/1.00      ( $false ),
% 3.37/1.00      inference(superposition,[status(thm)],[c_2222,c_2416]) ).
% 3.37/1.00  
% 3.37/1.00  
% 3.37/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.37/1.00  
% 3.37/1.00  ------                               Statistics
% 3.37/1.00  
% 3.37/1.00  ------ Selected
% 3.37/1.00  
% 3.37/1.00  total_time:                             0.121
% 3.37/1.00  
%------------------------------------------------------------------------------
