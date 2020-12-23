%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:57 EST 2020

% Result     : Theorem 3.94s
% Output     : CNFRefutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :   58 (  79 expanded)
%              Number of clauses        :   32 (  35 expanded)
%              Number of leaves         :    9 (  16 expanded)
%              Depth                    :   12
%              Number of atoms          :  104 ( 161 expanded)
%              Number of equality atoms :   47 (  55 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).

fof(f25,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f26,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_3,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_8615,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_8616,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_8740,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_8615,c_8616])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_8614,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_8618,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8846,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8614,c_8618])).

cnf(c_5,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_8861,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_8846,c_5])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_8617,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8904,plain,
    ( k4_xboole_0(k1_xboole_0,X0) != k1_xboole_0
    | r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8861,c_8617])).

cnf(c_3394,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3396,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3463,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3394,c_3396])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_3482,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3463,c_4])).

cnf(c_9784,plain,
    ( r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8904,c_3482])).

cnf(c_10182,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_8740,c_9784])).

cnf(c_2154,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_2156,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | ~ r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_2157,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X2,X1) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2225,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_tarski(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2156,c_2157])).

cnf(c_2242,plain,
    ( r1_xboole_0(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2154,c_2225])).

cnf(c_8,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_11,plain,
    ( r1_xboole_0(sK0,sK2) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10182,c_2242,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:13:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.94/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.94/1.00  
% 3.94/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.94/1.00  
% 3.94/1.00  ------  iProver source info
% 3.94/1.00  
% 3.94/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.94/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.94/1.00  git: non_committed_changes: false
% 3.94/1.00  git: last_make_outside_of_git: false
% 3.94/1.00  
% 3.94/1.00  ------ 
% 3.94/1.00  ------ Parsing...
% 3.94/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  ------ Proving...
% 3.94/1.00  ------ Problem Properties 
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  clauses                                 10
% 3.94/1.00  conjectures                             2
% 3.94/1.00  EPR                                     2
% 3.94/1.00  Horn                                    10
% 3.94/1.00  unary                                   5
% 3.94/1.00  binary                                  4
% 3.94/1.00  lits                                    16
% 3.94/1.00  lits eq                                 5
% 3.94/1.00  fd_pure                                 0
% 3.94/1.00  fd_pseudo                               0
% 3.94/1.00  fd_cond                                 0
% 3.94/1.00  fd_pseudo_cond                          0
% 3.94/1.00  AC symbols                              0
% 3.94/1.00  
% 3.94/1.00  ------ Input Options Time Limit: Unbounded
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing...
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.94/1.00  Current options:
% 3.94/1.00  ------ 
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing...
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing...
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing...
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing...
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing...
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing...
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing...
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing...
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/1.00  
% 3.94/1.00  ------ Proving...
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  % SZS status Theorem for theBenchmark.p
% 3.94/1.00  
% 3.94/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.94/1.00  
% 3.94/1.00  fof(f3,axiom,(
% 3.94/1.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.94/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/1.00  
% 3.94/1.00  fof(f20,plain,(
% 3.94/1.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.94/1.00    inference(cnf_transformation,[],[f3])).
% 3.94/1.00  
% 3.94/1.00  fof(f2,axiom,(
% 3.94/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.94/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/1.00  
% 3.94/1.00  fof(f10,plain,(
% 3.94/1.00    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.94/1.00    inference(ennf_transformation,[],[f2])).
% 3.94/1.00  
% 3.94/1.00  fof(f19,plain,(
% 3.94/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.94/1.00    inference(cnf_transformation,[],[f10])).
% 3.94/1.00  
% 3.94/1.00  fof(f8,conjecture,(
% 3.94/1.00    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.94/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/1.00  
% 3.94/1.00  fof(f9,negated_conjecture,(
% 3.94/1.00    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.94/1.00    inference(negated_conjecture,[],[f8])).
% 3.94/1.00  
% 3.94/1.00  fof(f13,plain,(
% 3.94/1.00    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.94/1.00    inference(ennf_transformation,[],[f9])).
% 3.94/1.00  
% 3.94/1.00  fof(f15,plain,(
% 3.94/1.00    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 3.94/1.00    introduced(choice_axiom,[])).
% 3.94/1.00  
% 3.94/1.00  fof(f16,plain,(
% 3.94/1.00    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 3.94/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).
% 3.94/1.00  
% 3.94/1.00  fof(f25,plain,(
% 3.94/1.00    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 3.94/1.00    inference(cnf_transformation,[],[f16])).
% 3.94/1.00  
% 3.94/1.00  fof(f1,axiom,(
% 3.94/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.94/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/1.00  
% 3.94/1.00  fof(f14,plain,(
% 3.94/1.00    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.94/1.00    inference(nnf_transformation,[],[f1])).
% 3.94/1.00  
% 3.94/1.00  fof(f18,plain,(
% 3.94/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.94/1.00    inference(cnf_transformation,[],[f14])).
% 3.94/1.00  
% 3.94/1.00  fof(f5,axiom,(
% 3.94/1.00    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.94/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/1.00  
% 3.94/1.00  fof(f22,plain,(
% 3.94/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.94/1.00    inference(cnf_transformation,[],[f5])).
% 3.94/1.00  
% 3.94/1.00  fof(f17,plain,(
% 3.94/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.94/1.00    inference(cnf_transformation,[],[f14])).
% 3.94/1.00  
% 3.94/1.00  fof(f4,axiom,(
% 3.94/1.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.94/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/1.00  
% 3.94/1.00  fof(f21,plain,(
% 3.94/1.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.94/1.00    inference(cnf_transformation,[],[f4])).
% 3.94/1.00  
% 3.94/1.00  fof(f7,axiom,(
% 3.94/1.00    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.94/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/1.00  
% 3.94/1.00  fof(f24,plain,(
% 3.94/1.00    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.94/1.00    inference(cnf_transformation,[],[f7])).
% 3.94/1.00  
% 3.94/1.00  fof(f6,axiom,(
% 3.94/1.00    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 3.94/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/1.00  
% 3.94/1.00  fof(f11,plain,(
% 3.94/1.00    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.94/1.00    inference(ennf_transformation,[],[f6])).
% 3.94/1.00  
% 3.94/1.00  fof(f12,plain,(
% 3.94/1.00    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 3.94/1.00    inference(flattening,[],[f11])).
% 3.94/1.00  
% 3.94/1.00  fof(f23,plain,(
% 3.94/1.00    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.94/1.00    inference(cnf_transformation,[],[f12])).
% 3.94/1.00  
% 3.94/1.00  fof(f26,plain,(
% 3.94/1.00    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 3.94/1.00    inference(cnf_transformation,[],[f16])).
% 3.94/1.00  
% 3.94/1.00  cnf(c_3,plain,
% 3.94/1.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.94/1.00      inference(cnf_transformation,[],[f20]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_8615,plain,
% 3.94/1.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 3.94/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_2,plain,
% 3.94/1.00      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 3.94/1.00      inference(cnf_transformation,[],[f19]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_8616,plain,
% 3.94/1.00      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 3.94/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_8740,plain,
% 3.94/1.00      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_8615,c_8616]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_9,negated_conjecture,
% 3.94/1.00      ( r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
% 3.94/1.00      inference(cnf_transformation,[],[f25]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_8614,plain,
% 3.94/1.00      ( r1_tarski(sK0,k4_xboole_0(sK1,sK2)) = iProver_top ),
% 3.94/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_0,plain,
% 3.94/1.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.94/1.00      inference(cnf_transformation,[],[f18]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_8618,plain,
% 3.94/1.00      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 3.94/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.94/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_8846,plain,
% 3.94/1.00      ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_8614,c_8618]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_5,plain,
% 3.94/1.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.94/1.00      inference(cnf_transformation,[],[f22]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_8861,plain,
% 3.94/1.00      ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_8846,c_5]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_1,plain,
% 3.94/1.00      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 3.94/1.00      inference(cnf_transformation,[],[f17]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_8617,plain,
% 3.94/1.00      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 3.94/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.94/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_8904,plain,
% 3.94/1.00      ( k4_xboole_0(k1_xboole_0,X0) != k1_xboole_0
% 3.94/1.00      | r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = iProver_top ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_8861,c_8617]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_3394,plain,
% 3.94/1.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 3.94/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_3396,plain,
% 3.94/1.00      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 3.94/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.94/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_3463,plain,
% 3.94/1.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_3394,c_3396]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_4,plain,
% 3.94/1.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.94/1.00      inference(cnf_transformation,[],[f21]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_3482,plain,
% 3.94/1.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_3463,c_4]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_9784,plain,
% 3.94/1.00      ( r1_tarski(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = iProver_top ),
% 3.94/1.00      inference(global_propositional_subsumption,
% 3.94/1.00                [status(thm)],
% 3.94/1.00                [c_8904,c_3482]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_10182,plain,
% 3.94/1.00      ( r1_tarski(sK0,sK1) = iProver_top ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_8740,c_9784]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_2154,plain,
% 3.94/1.00      ( r1_tarski(sK0,k4_xboole_0(sK1,sK2)) = iProver_top ),
% 3.94/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_7,plain,
% 3.94/1.00      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 3.94/1.00      inference(cnf_transformation,[],[f24]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_2156,plain,
% 3.94/1.00      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 3.94/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_6,plain,
% 3.94/1.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | ~ r1_tarski(X2,X0) ),
% 3.94/1.00      inference(cnf_transformation,[],[f23]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_2157,plain,
% 3.94/1.00      ( r1_xboole_0(X0,X1) != iProver_top
% 3.94/1.00      | r1_xboole_0(X2,X1) = iProver_top
% 3.94/1.00      | r1_tarski(X2,X0) != iProver_top ),
% 3.94/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_2225,plain,
% 3.94/1.00      ( r1_xboole_0(X0,X1) = iProver_top
% 3.94/1.00      | r1_tarski(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_2156,c_2157]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_2242,plain,
% 3.94/1.00      ( r1_xboole_0(sK0,sK2) = iProver_top ),
% 3.94/1.00      inference(superposition,[status(thm)],[c_2154,c_2225]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_8,negated_conjecture,
% 3.94/1.00      ( ~ r1_xboole_0(sK0,sK2) | ~ r1_tarski(sK0,sK1) ),
% 3.94/1.00      inference(cnf_transformation,[],[f26]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(c_11,plain,
% 3.94/1.00      ( r1_xboole_0(sK0,sK2) != iProver_top
% 3.94/1.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 3.94/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.94/1.00  
% 3.94/1.00  cnf(contradiction,plain,
% 3.94/1.00      ( $false ),
% 3.94/1.00      inference(minisat,[status(thm)],[c_10182,c_2242,c_11]) ).
% 3.94/1.00  
% 3.94/1.00  
% 3.94/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.94/1.00  
% 3.94/1.00  ------                               Statistics
% 3.94/1.00  
% 3.94/1.00  ------ Selected
% 3.94/1.00  
% 3.94/1.00  total_time:                             0.382
% 3.94/1.00  
%------------------------------------------------------------------------------
