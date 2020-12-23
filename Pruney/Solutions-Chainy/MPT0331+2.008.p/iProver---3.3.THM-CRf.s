%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:14 EST 2020

% Result     : Theorem 15.36s
% Output     : CNFRefutation 15.36s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 132 expanded)
%              Number of clauses        :   34 (  44 expanded)
%              Number of leaves         :   11 (  30 expanded)
%              Depth                    :   13
%              Number of atoms          :  138 ( 266 expanded)
%              Number of equality atoms :   78 ( 143 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f15])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f22,f31,f31])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f25,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(flattening,[],[f18])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) = k2_enumset1(X0,X0,X0,X1)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f37,f41,f41])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( k4_xboole_0(sK2,k2_tarski(sK0,sK1)) != sK2
      & ~ r2_hidden(sK1,sK2)
      & ~ r2_hidden(sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( k4_xboole_0(sK2,k2_tarski(sK0,sK1)) != sK2
    & ~ r2_hidden(sK1,sK2)
    & ~ r2_hidden(sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f20])).

fof(f39,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f40,plain,(
    k4_xboole_0(sK2,k2_tarski(sK0,sK1)) != sK2 ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)) != sK2 ),
    inference(definition_unfolding,[],[f40,f41])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_52803,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_52802,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_53417,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_52803,c_52802])).

cnf(c_7,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_52800,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_53554,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_53417,c_52800])).

cnf(c_53568,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_53554,c_52802])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_52801,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_53269,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_tarski(X1,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_52801])).

cnf(c_53695,plain,
    ( r1_tarski(X0,k4_xboole_0(X0,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_53568,c_53269])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_52804,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_54260,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_tarski(X0,k4_xboole_0(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_52800,c_52804])).

cnf(c_57375,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_53695,c_54260])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | k4_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) = k2_enumset1(X0,X0,X0,X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_52799,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) = k2_enumset1(X0,X0,X0,X1)
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_52798,plain,
    ( r2_hidden(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_54439,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,sK1),sK2) = k2_enumset1(X0,X0,X0,sK1)
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_52799,c_52798])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_52797,plain,
    ( r2_hidden(sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_54648,plain,
    ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) = k2_enumset1(sK0,sK0,sK0,sK1) ),
    inference(superposition,[status(thm)],[c_54439,c_52797])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_53121,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_8])).

cnf(c_54921,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1))) = k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_54648,c_53121])).

cnf(c_54927,plain,
    ( k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_54921,c_53417])).

cnf(c_13,negated_conjecture,
    ( k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)) != sK2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_57932,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) != sK2 ),
    inference(demodulation,[status(thm)],[c_54927,c_13])).

cnf(c_62088,plain,
    ( sK2 != sK2 ),
    inference(demodulation,[status(thm)],[c_57375,c_57932])).

cnf(c_62095,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_62088])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:21:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.36/2.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.36/2.49  
% 15.36/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.36/2.49  
% 15.36/2.49  ------  iProver source info
% 15.36/2.49  
% 15.36/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.36/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.36/2.49  git: non_committed_changes: false
% 15.36/2.49  git: last_make_outside_of_git: false
% 15.36/2.49  
% 15.36/2.49  ------ 
% 15.36/2.49  ------ Parsing...
% 15.36/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.36/2.49  
% 15.36/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 15.36/2.49  
% 15.36/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.36/2.49  
% 15.36/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.36/2.49  ------ Proving...
% 15.36/2.49  ------ Problem Properties 
% 15.36/2.49  
% 15.36/2.49  
% 15.36/2.49  clauses                                 15
% 15.36/2.49  conjectures                             3
% 15.36/2.49  EPR                                     4
% 15.36/2.49  Horn                                    14
% 15.36/2.49  unary                                   9
% 15.36/2.49  binary                                  4
% 15.36/2.49  lits                                    23
% 15.36/2.49  lits eq                                 11
% 15.36/2.49  fd_pure                                 0
% 15.36/2.49  fd_pseudo                               0
% 15.36/2.49  fd_cond                                 0
% 15.36/2.49  fd_pseudo_cond                          1
% 15.36/2.49  AC symbols                              0
% 15.36/2.49  
% 15.36/2.49  ------ Input Options Time Limit: Unbounded
% 15.36/2.49  
% 15.36/2.49  
% 15.36/2.49  
% 15.36/2.49  
% 15.36/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 15.36/2.49  Current options:
% 15.36/2.49  ------ 
% 15.36/2.49  
% 15.36/2.49  
% 15.36/2.49  
% 15.36/2.49  
% 15.36/2.49  ------ Proving...
% 15.36/2.49  
% 15.36/2.49  
% 15.36/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.36/2.49  
% 15.36/2.49  ------ Proving...
% 15.36/2.49  
% 15.36/2.49  
% 15.36/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.36/2.49  
% 15.36/2.49  ------ Proving...
% 15.36/2.49  
% 15.36/2.49  
% 15.36/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.36/2.49  
% 15.36/2.49  ------ Proving...
% 15.36/2.49  
% 15.36/2.49  
% 15.36/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.36/2.49  
% 15.36/2.49  ------ Proving...
% 15.36/2.49  
% 15.36/2.49  
% 15.36/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.36/2.49  
% 15.36/2.49  ------ Proving...
% 15.36/2.49  
% 15.36/2.49  
% 15.36/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.36/2.49  
% 15.36/2.49  ------ Proving...
% 15.36/2.49  
% 15.36/2.49  
% 15.36/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.36/2.49  
% 15.36/2.49  ------ Proving...
% 15.36/2.49  
% 15.36/2.49  
% 15.36/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.36/2.49  
% 15.36/2.49  ------ Proving...
% 15.36/2.49  
% 15.36/2.49  
% 15.36/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.36/2.49  
% 15.36/2.49  ------ Proving...
% 15.36/2.49  
% 15.36/2.49  
% 15.36/2.49  % SZS status Theorem for theBenchmark.p
% 15.36/2.49  
% 15.36/2.49   Resolution empty clause
% 15.36/2.49  
% 15.36/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.36/2.49  
% 15.36/2.49  fof(f2,axiom,(
% 15.36/2.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.36/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.36/2.49  
% 15.36/2.49  fof(f15,plain,(
% 15.36/2.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.36/2.49    inference(nnf_transformation,[],[f2])).
% 15.36/2.49  
% 15.36/2.49  fof(f16,plain,(
% 15.36/2.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.36/2.49    inference(flattening,[],[f15])).
% 15.36/2.49  
% 15.36/2.49  fof(f23,plain,(
% 15.36/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 15.36/2.49    inference(cnf_transformation,[],[f16])).
% 15.36/2.49  
% 15.36/2.49  fof(f51,plain,(
% 15.36/2.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.36/2.49    inference(equality_resolution,[],[f23])).
% 15.36/2.49  
% 15.36/2.49  fof(f3,axiom,(
% 15.36/2.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 15.36/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.36/2.49  
% 15.36/2.49  fof(f17,plain,(
% 15.36/2.49    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 15.36/2.49    inference(nnf_transformation,[],[f3])).
% 15.36/2.49  
% 15.36/2.49  fof(f27,plain,(
% 15.36/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 15.36/2.49    inference(cnf_transformation,[],[f17])).
% 15.36/2.49  
% 15.36/2.49  fof(f5,axiom,(
% 15.36/2.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 15.36/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.36/2.49  
% 15.36/2.49  fof(f29,plain,(
% 15.36/2.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 15.36/2.49    inference(cnf_transformation,[],[f5])).
% 15.36/2.49  
% 15.36/2.49  fof(f1,axiom,(
% 15.36/2.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.36/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.36/2.49  
% 15.36/2.49  fof(f22,plain,(
% 15.36/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.36/2.49    inference(cnf_transformation,[],[f1])).
% 15.36/2.49  
% 15.36/2.49  fof(f7,axiom,(
% 15.36/2.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 15.36/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.36/2.49  
% 15.36/2.49  fof(f31,plain,(
% 15.36/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 15.36/2.49    inference(cnf_transformation,[],[f7])).
% 15.36/2.49  
% 15.36/2.49  fof(f43,plain,(
% 15.36/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 15.36/2.49    inference(definition_unfolding,[],[f22,f31,f31])).
% 15.36/2.49  
% 15.36/2.49  fof(f26,plain,(
% 15.36/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 15.36/2.49    inference(cnf_transformation,[],[f17])).
% 15.36/2.49  
% 15.36/2.49  fof(f25,plain,(
% 15.36/2.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.36/2.49    inference(cnf_transformation,[],[f16])).
% 15.36/2.49  
% 15.36/2.49  fof(f11,axiom,(
% 15.36/2.49    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 15.36/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.36/2.49  
% 15.36/2.49  fof(f18,plain,(
% 15.36/2.49    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 15.36/2.49    inference(nnf_transformation,[],[f11])).
% 15.36/2.49  
% 15.36/2.49  fof(f19,plain,(
% 15.36/2.49    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 15.36/2.49    inference(flattening,[],[f18])).
% 15.36/2.49  
% 15.36/2.49  fof(f37,plain,(
% 15.36/2.49    ( ! [X2,X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 15.36/2.49    inference(cnf_transformation,[],[f19])).
% 15.36/2.49  
% 15.36/2.49  fof(f9,axiom,(
% 15.36/2.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 15.36/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.36/2.49  
% 15.36/2.49  fof(f33,plain,(
% 15.36/2.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 15.36/2.49    inference(cnf_transformation,[],[f9])).
% 15.36/2.49  
% 15.36/2.49  fof(f10,axiom,(
% 15.36/2.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.36/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.36/2.49  
% 15.36/2.49  fof(f34,plain,(
% 15.36/2.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.36/2.49    inference(cnf_transformation,[],[f10])).
% 15.36/2.49  
% 15.36/2.49  fof(f41,plain,(
% 15.36/2.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 15.36/2.49    inference(definition_unfolding,[],[f33,f34])).
% 15.36/2.49  
% 15.36/2.49  fof(f46,plain,(
% 15.36/2.49    ( ! [X2,X0,X1] : (k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) = k2_enumset1(X0,X0,X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 15.36/2.49    inference(definition_unfolding,[],[f37,f41,f41])).
% 15.36/2.49  
% 15.36/2.49  fof(f12,conjecture,(
% 15.36/2.49    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 15.36/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.36/2.49  
% 15.36/2.49  fof(f13,negated_conjecture,(
% 15.36/2.49    ~! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 15.36/2.49    inference(negated_conjecture,[],[f12])).
% 15.36/2.49  
% 15.36/2.49  fof(f14,plain,(
% 15.36/2.49    ? [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 15.36/2.49    inference(ennf_transformation,[],[f13])).
% 15.36/2.49  
% 15.36/2.49  fof(f20,plain,(
% 15.36/2.49    ? [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) => (k4_xboole_0(sK2,k2_tarski(sK0,sK1)) != sK2 & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2))),
% 15.36/2.49    introduced(choice_axiom,[])).
% 15.36/2.49  
% 15.36/2.49  fof(f21,plain,(
% 15.36/2.49    k4_xboole_0(sK2,k2_tarski(sK0,sK1)) != sK2 & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)),
% 15.36/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f20])).
% 15.36/2.49  
% 15.36/2.49  fof(f39,plain,(
% 15.36/2.49    ~r2_hidden(sK1,sK2)),
% 15.36/2.49    inference(cnf_transformation,[],[f21])).
% 15.36/2.49  
% 15.36/2.49  fof(f38,plain,(
% 15.36/2.49    ~r2_hidden(sK0,sK2)),
% 15.36/2.49    inference(cnf_transformation,[],[f21])).
% 15.36/2.49  
% 15.36/2.49  fof(f6,axiom,(
% 15.36/2.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 15.36/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.36/2.49  
% 15.36/2.49  fof(f30,plain,(
% 15.36/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 15.36/2.49    inference(cnf_transformation,[],[f6])).
% 15.36/2.49  
% 15.36/2.49  fof(f44,plain,(
% 15.36/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 15.36/2.49    inference(definition_unfolding,[],[f30,f31])).
% 15.36/2.49  
% 15.36/2.49  fof(f40,plain,(
% 15.36/2.49    k4_xboole_0(sK2,k2_tarski(sK0,sK1)) != sK2),
% 15.36/2.49    inference(cnf_transformation,[],[f21])).
% 15.36/2.49  
% 15.36/2.49  fof(f49,plain,(
% 15.36/2.49    k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)) != sK2),
% 15.36/2.49    inference(definition_unfolding,[],[f40,f41])).
% 15.36/2.49  
% 15.36/2.49  cnf(c_4,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f51]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_52803,plain,
% 15.36/2.49      ( r1_tarski(X0,X0) = iProver_top ),
% 15.36/2.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_5,plain,
% 15.36/2.49      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 15.36/2.49      inference(cnf_transformation,[],[f27]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_52802,plain,
% 15.36/2.49      ( k4_xboole_0(X0,X1) = k1_xboole_0 | r1_tarski(X0,X1) != iProver_top ),
% 15.36/2.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_53417,plain,
% 15.36/2.49      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 15.36/2.49      inference(superposition,[status(thm)],[c_52803,c_52802]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_7,plain,
% 15.36/2.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 15.36/2.49      inference(cnf_transformation,[],[f29]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_52800,plain,
% 15.36/2.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 15.36/2.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_53554,plain,
% 15.36/2.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 15.36/2.49      inference(superposition,[status(thm)],[c_53417,c_52800]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_53568,plain,
% 15.36/2.49      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 15.36/2.49      inference(superposition,[status(thm)],[c_53554,c_52802]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_1,plain,
% 15.36/2.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 15.36/2.49      inference(cnf_transformation,[],[f43]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_6,plain,
% 15.36/2.49      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 15.36/2.49      inference(cnf_transformation,[],[f26]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_52801,plain,
% 15.36/2.49      ( k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1) = iProver_top ),
% 15.36/2.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_53269,plain,
% 15.36/2.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 15.36/2.49      | r1_tarski(X1,k4_xboole_0(X1,X0)) = iProver_top ),
% 15.36/2.49      inference(superposition,[status(thm)],[c_1,c_52801]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_53695,plain,
% 15.36/2.49      ( r1_tarski(X0,k4_xboole_0(X0,k1_xboole_0)) = iProver_top ),
% 15.36/2.49      inference(superposition,[status(thm)],[c_53568,c_53269]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_2,plain,
% 15.36/2.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 15.36/2.49      inference(cnf_transformation,[],[f25]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_52804,plain,
% 15.36/2.49      ( X0 = X1
% 15.36/2.49      | r1_tarski(X0,X1) != iProver_top
% 15.36/2.49      | r1_tarski(X1,X0) != iProver_top ),
% 15.36/2.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_54260,plain,
% 15.36/2.49      ( k4_xboole_0(X0,X1) = X0
% 15.36/2.49      | r1_tarski(X0,k4_xboole_0(X0,X1)) != iProver_top ),
% 15.36/2.49      inference(superposition,[status(thm)],[c_52800,c_52804]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_57375,plain,
% 15.36/2.49      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.36/2.49      inference(superposition,[status(thm)],[c_53695,c_54260]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_10,plain,
% 15.36/2.49      ( r2_hidden(X0,X1)
% 15.36/2.49      | r2_hidden(X2,X1)
% 15.36/2.49      | k4_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) = k2_enumset1(X0,X0,X0,X2) ),
% 15.36/2.49      inference(cnf_transformation,[],[f46]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_52799,plain,
% 15.36/2.49      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) = k2_enumset1(X0,X0,X0,X1)
% 15.36/2.49      | r2_hidden(X0,X2) = iProver_top
% 15.36/2.49      | r2_hidden(X1,X2) = iProver_top ),
% 15.36/2.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_14,negated_conjecture,
% 15.36/2.49      ( ~ r2_hidden(sK1,sK2) ),
% 15.36/2.49      inference(cnf_transformation,[],[f39]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_52798,plain,
% 15.36/2.49      ( r2_hidden(sK1,sK2) != iProver_top ),
% 15.36/2.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_54439,plain,
% 15.36/2.49      ( k4_xboole_0(k2_enumset1(X0,X0,X0,sK1),sK2) = k2_enumset1(X0,X0,X0,sK1)
% 15.36/2.49      | r2_hidden(X0,sK2) = iProver_top ),
% 15.36/2.49      inference(superposition,[status(thm)],[c_52799,c_52798]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_15,negated_conjecture,
% 15.36/2.49      ( ~ r2_hidden(sK0,sK2) ),
% 15.36/2.49      inference(cnf_transformation,[],[f38]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_52797,plain,
% 15.36/2.49      ( r2_hidden(sK0,sK2) != iProver_top ),
% 15.36/2.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_54648,plain,
% 15.36/2.49      ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) = k2_enumset1(sK0,sK0,sK0,sK1) ),
% 15.36/2.49      inference(superposition,[status(thm)],[c_54439,c_52797]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_8,plain,
% 15.36/2.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 15.36/2.49      inference(cnf_transformation,[],[f44]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_53121,plain,
% 15.36/2.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 15.36/2.49      inference(superposition,[status(thm)],[c_1,c_8]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_54921,plain,
% 15.36/2.49      ( k4_xboole_0(sK2,k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1))) = k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)) ),
% 15.36/2.49      inference(superposition,[status(thm)],[c_54648,c_53121]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_54927,plain,
% 15.36/2.49      ( k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)) = k4_xboole_0(sK2,k1_xboole_0) ),
% 15.36/2.49      inference(demodulation,[status(thm)],[c_54921,c_53417]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_13,negated_conjecture,
% 15.36/2.49      ( k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)) != sK2 ),
% 15.36/2.49      inference(cnf_transformation,[],[f49]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_57932,plain,
% 15.36/2.49      ( k4_xboole_0(sK2,k1_xboole_0) != sK2 ),
% 15.36/2.49      inference(demodulation,[status(thm)],[c_54927,c_13]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_62088,plain,
% 15.36/2.49      ( sK2 != sK2 ),
% 15.36/2.49      inference(demodulation,[status(thm)],[c_57375,c_57932]) ).
% 15.36/2.49  
% 15.36/2.49  cnf(c_62095,plain,
% 15.36/2.49      ( $false ),
% 15.36/2.49      inference(equality_resolution_simp,[status(thm)],[c_62088]) ).
% 15.36/2.49  
% 15.36/2.49  
% 15.36/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.36/2.49  
% 15.36/2.49  ------                               Statistics
% 15.36/2.49  
% 15.36/2.49  ------ Selected
% 15.36/2.49  
% 15.36/2.49  total_time:                             1.855
% 15.36/2.49  
%------------------------------------------------------------------------------
