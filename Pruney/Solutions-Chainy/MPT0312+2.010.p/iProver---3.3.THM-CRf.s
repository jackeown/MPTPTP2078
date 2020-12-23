%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:13 EST 2020

% Result     : Theorem 23.94s
% Output     : CNFRefutation 23.94s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 111 expanded)
%              Number of clauses        :   28 (  44 expanded)
%              Number of leaves         :    7 (  18 expanded)
%              Depth                    :   15
%              Number of atoms          :  112 ( 292 expanded)
%              Number of equality atoms :   53 ( 119 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(X0,X2) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) != k2_zfmisc_1(X0,X2)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) != k2_zfmisc_1(X0,X2)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3] :
        ( k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) != k2_zfmisc_1(X0,X2)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) != k2_zfmisc_1(sK0,sK2)
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) != k2_zfmisc_1(sK0,sK2)
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f15])).

fof(f24,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f13])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f26,plain,(
    k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) != k2_zfmisc_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f25,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_11804,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_11808,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_11807,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_11881,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11808,c_11807])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_11806,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k3_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_11809,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_12205,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X1),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_11806,c_11809])).

cnf(c_15443,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11881,c_12205])).

cnf(c_19,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_89574,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k3_xboole_0(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15443,c_19])).

cnf(c_89575,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_89574])).

cnf(c_89583,plain,
    ( k3_xboole_0(sK0,sK1) = sK0 ),
    inference(superposition,[status(thm)],[c_11804,c_89575])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_91722,plain,
    ( k3_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X1)) = k2_zfmisc_1(sK0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_89583,c_6])).

cnf(c_7,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) != k2_zfmisc_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_98457,plain,
    ( k2_zfmisc_1(sK0,k3_xboole_0(sK3,sK2)) != k2_zfmisc_1(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_91722,c_7])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_11805,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_89582,plain,
    ( k3_xboole_0(sK2,sK3) = sK2 ),
    inference(superposition,[status(thm)],[c_11805,c_89575])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_90388,plain,
    ( k3_xboole_0(sK3,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_89582,c_0])).

cnf(c_98458,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,sK2) ),
    inference(light_normalisation,[status(thm)],[c_98457,c_90388])).

cnf(c_98459,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_98458])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:30:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 23.94/3.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.94/3.48  
% 23.94/3.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.94/3.48  
% 23.94/3.48  ------  iProver source info
% 23.94/3.48  
% 23.94/3.48  git: date: 2020-06-30 10:37:57 +0100
% 23.94/3.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.94/3.48  git: non_committed_changes: false
% 23.94/3.48  git: last_make_outside_of_git: false
% 23.94/3.48  
% 23.94/3.48  ------ 
% 23.94/3.48  ------ Parsing...
% 23.94/3.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.94/3.48  
% 23.94/3.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 23.94/3.48  
% 23.94/3.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.94/3.48  
% 23.94/3.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.94/3.48  ------ Proving...
% 23.94/3.48  ------ Problem Properties 
% 23.94/3.48  
% 23.94/3.48  
% 23.94/3.48  clauses                                 9
% 23.94/3.48  conjectures                             3
% 23.94/3.48  EPR                                     4
% 23.94/3.48  Horn                                    9
% 23.94/3.48  unary                                   6
% 23.94/3.48  binary                                  1
% 23.94/3.48  lits                                    14
% 23.94/3.48  lits eq                                 4
% 23.94/3.48  fd_pure                                 0
% 23.94/3.48  fd_pseudo                               0
% 23.94/3.48  fd_cond                                 0
% 23.94/3.48  fd_pseudo_cond                          1
% 23.94/3.48  AC symbols                              0
% 23.94/3.48  
% 23.94/3.48  ------ Input Options Time Limit: Unbounded
% 23.94/3.48  
% 23.94/3.48  
% 23.94/3.48  
% 23.94/3.48  
% 23.94/3.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 23.94/3.48  Current options:
% 23.94/3.48  ------ 
% 23.94/3.48  
% 23.94/3.48  
% 23.94/3.48  
% 23.94/3.48  
% 23.94/3.48  ------ Proving...
% 23.94/3.48  
% 23.94/3.48  
% 23.94/3.48  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.94/3.48  
% 23.94/3.48  ------ Proving...
% 23.94/3.48  
% 23.94/3.48  
% 23.94/3.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.94/3.48  
% 23.94/3.48  ------ Proving...
% 23.94/3.48  
% 23.94/3.48  
% 23.94/3.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.94/3.48  
% 23.94/3.48  ------ Proving...
% 23.94/3.48  
% 23.94/3.48  
% 23.94/3.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.94/3.48  
% 23.94/3.48  ------ Proving...
% 23.94/3.48  
% 23.94/3.48  
% 23.94/3.48  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.94/3.48  
% 23.94/3.48  ------ Proving...
% 23.94/3.48  
% 23.94/3.48  
% 23.94/3.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.94/3.48  
% 23.94/3.48  ------ Proving...
% 23.94/3.48  
% 23.94/3.48  
% 23.94/3.48  % SZS status Theorem for theBenchmark.p
% 23.94/3.48  
% 23.94/3.48   Resolution empty clause
% 23.94/3.48  
% 23.94/3.48  % SZS output start CNFRefutation for theBenchmark.p
% 23.94/3.48  
% 23.94/3.48  fof(f6,conjecture,(
% 23.94/3.48    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(X0,X2))),
% 23.94/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.94/3.48  
% 23.94/3.48  fof(f7,negated_conjecture,(
% 23.94/3.48    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(X0,X2))),
% 23.94/3.48    inference(negated_conjecture,[],[f6])).
% 23.94/3.48  
% 23.94/3.48  fof(f11,plain,(
% 23.94/3.48    ? [X0,X1,X2,X3] : (k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) != k2_zfmisc_1(X0,X2) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 23.94/3.48    inference(ennf_transformation,[],[f7])).
% 23.94/3.48  
% 23.94/3.48  fof(f12,plain,(
% 23.94/3.48    ? [X0,X1,X2,X3] : (k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) != k2_zfmisc_1(X0,X2) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 23.94/3.48    inference(flattening,[],[f11])).
% 23.94/3.48  
% 23.94/3.48  fof(f15,plain,(
% 23.94/3.48    ? [X0,X1,X2,X3] : (k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) != k2_zfmisc_1(X0,X2) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => (k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) != k2_zfmisc_1(sK0,sK2) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1))),
% 23.94/3.48    introduced(choice_axiom,[])).
% 23.94/3.48  
% 23.94/3.48  fof(f16,plain,(
% 23.94/3.48    k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) != k2_zfmisc_1(sK0,sK2) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1)),
% 23.94/3.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f15])).
% 23.94/3.48  
% 23.94/3.48  fof(f24,plain,(
% 23.94/3.48    r1_tarski(sK0,sK1)),
% 23.94/3.48    inference(cnf_transformation,[],[f16])).
% 23.94/3.48  
% 23.94/3.48  fof(f2,axiom,(
% 23.94/3.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 23.94/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.94/3.48  
% 23.94/3.48  fof(f13,plain,(
% 23.94/3.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.94/3.48    inference(nnf_transformation,[],[f2])).
% 23.94/3.48  
% 23.94/3.48  fof(f14,plain,(
% 23.94/3.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.94/3.48    inference(flattening,[],[f13])).
% 23.94/3.48  
% 23.94/3.48  fof(f18,plain,(
% 23.94/3.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 23.94/3.48    inference(cnf_transformation,[],[f14])).
% 23.94/3.48  
% 23.94/3.48  fof(f28,plain,(
% 23.94/3.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 23.94/3.48    inference(equality_resolution,[],[f18])).
% 23.94/3.48  
% 23.94/3.48  fof(f3,axiom,(
% 23.94/3.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 23.94/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.94/3.48  
% 23.94/3.48  fof(f8,plain,(
% 23.94/3.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 23.94/3.48    inference(ennf_transformation,[],[f3])).
% 23.94/3.48  
% 23.94/3.48  fof(f21,plain,(
% 23.94/3.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 23.94/3.48    inference(cnf_transformation,[],[f8])).
% 23.94/3.48  
% 23.94/3.48  fof(f4,axiom,(
% 23.94/3.48    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 23.94/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.94/3.48  
% 23.94/3.48  fof(f9,plain,(
% 23.94/3.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 23.94/3.48    inference(ennf_transformation,[],[f4])).
% 23.94/3.48  
% 23.94/3.48  fof(f10,plain,(
% 23.94/3.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 23.94/3.48    inference(flattening,[],[f9])).
% 23.94/3.48  
% 23.94/3.48  fof(f22,plain,(
% 23.94/3.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 23.94/3.48    inference(cnf_transformation,[],[f10])).
% 23.94/3.48  
% 23.94/3.48  fof(f20,plain,(
% 23.94/3.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 23.94/3.48    inference(cnf_transformation,[],[f14])).
% 23.94/3.48  
% 23.94/3.48  fof(f5,axiom,(
% 23.94/3.48    ! [X0,X1,X2,X3] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3))),
% 23.94/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.94/3.48  
% 23.94/3.48  fof(f23,plain,(
% 23.94/3.48    ( ! [X2,X0,X3,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3))) )),
% 23.94/3.48    inference(cnf_transformation,[],[f5])).
% 23.94/3.48  
% 23.94/3.48  fof(f26,plain,(
% 23.94/3.48    k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) != k2_zfmisc_1(sK0,sK2)),
% 23.94/3.48    inference(cnf_transformation,[],[f16])).
% 23.94/3.48  
% 23.94/3.48  fof(f25,plain,(
% 23.94/3.48    r1_tarski(sK2,sK3)),
% 23.94/3.48    inference(cnf_transformation,[],[f16])).
% 23.94/3.48  
% 23.94/3.48  fof(f1,axiom,(
% 23.94/3.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 23.94/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.94/3.48  
% 23.94/3.48  fof(f17,plain,(
% 23.94/3.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 23.94/3.48    inference(cnf_transformation,[],[f1])).
% 23.94/3.48  
% 23.94/3.48  cnf(c_9,negated_conjecture,
% 23.94/3.48      ( r1_tarski(sK0,sK1) ),
% 23.94/3.48      inference(cnf_transformation,[],[f24]) ).
% 23.94/3.48  
% 23.94/3.48  cnf(c_11804,plain,
% 23.94/3.48      ( r1_tarski(sK0,sK1) = iProver_top ),
% 23.94/3.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 23.94/3.48  
% 23.94/3.48  cnf(c_3,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f28]) ).
% 23.94/3.48  
% 23.94/3.48  cnf(c_11808,plain,
% 23.94/3.48      ( r1_tarski(X0,X0) = iProver_top ),
% 23.94/3.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 23.94/3.48  
% 23.94/3.48  cnf(c_4,plain,
% 23.94/3.48      ( r1_tarski(X0,X1) | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ),
% 23.94/3.48      inference(cnf_transformation,[],[f21]) ).
% 23.94/3.48  
% 23.94/3.48  cnf(c_11807,plain,
% 23.94/3.48      ( r1_tarski(X0,X1) = iProver_top
% 23.94/3.48      | r1_tarski(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 23.94/3.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 23.94/3.48  
% 23.94/3.48  cnf(c_11881,plain,
% 23.94/3.48      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 23.94/3.48      inference(superposition,[status(thm)],[c_11808,c_11807]) ).
% 23.94/3.48  
% 23.94/3.48  cnf(c_5,plain,
% 23.94/3.48      ( ~ r1_tarski(X0,X1)
% 23.94/3.48      | ~ r1_tarski(X0,X2)
% 23.94/3.48      | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
% 23.94/3.48      inference(cnf_transformation,[],[f22]) ).
% 23.94/3.48  
% 23.94/3.48  cnf(c_11806,plain,
% 23.94/3.48      ( r1_tarski(X0,X1) != iProver_top
% 23.94/3.48      | r1_tarski(X0,X2) != iProver_top
% 23.94/3.48      | r1_tarski(X0,k3_xboole_0(X1,X2)) = iProver_top ),
% 23.94/3.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 23.94/3.48  
% 23.94/3.48  cnf(c_1,plain,
% 23.94/3.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 23.94/3.48      inference(cnf_transformation,[],[f20]) ).
% 23.94/3.48  
% 23.94/3.48  cnf(c_11809,plain,
% 23.94/3.48      ( X0 = X1
% 23.94/3.48      | r1_tarski(X0,X1) != iProver_top
% 23.94/3.48      | r1_tarski(X1,X0) != iProver_top ),
% 23.94/3.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.94/3.48  
% 23.94/3.48  cnf(c_12205,plain,
% 23.94/3.48      ( k3_xboole_0(X0,X1) = X2
% 23.94/3.48      | r1_tarski(X2,X0) != iProver_top
% 23.94/3.48      | r1_tarski(X2,X1) != iProver_top
% 23.94/3.48      | r1_tarski(k3_xboole_0(X0,X1),X2) != iProver_top ),
% 23.94/3.48      inference(superposition,[status(thm)],[c_11806,c_11809]) ).
% 23.94/3.48  
% 23.94/3.48  cnf(c_15443,plain,
% 23.94/3.48      ( k3_xboole_0(X0,X1) = X0
% 23.94/3.48      | r1_tarski(X0,X1) != iProver_top
% 23.94/3.48      | r1_tarski(X0,X0) != iProver_top ),
% 23.94/3.48      inference(superposition,[status(thm)],[c_11881,c_12205]) ).
% 23.94/3.48  
% 23.94/3.48  cnf(c_19,plain,
% 23.94/3.48      ( r1_tarski(X0,X0) = iProver_top ),
% 23.94/3.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 23.94/3.48  
% 23.94/3.48  cnf(c_89574,plain,
% 23.94/3.48      ( r1_tarski(X0,X1) != iProver_top | k3_xboole_0(X0,X1) = X0 ),
% 23.94/3.48      inference(global_propositional_subsumption,[status(thm)],[c_15443,c_19]) ).
% 23.94/3.48  
% 23.94/3.48  cnf(c_89575,plain,
% 23.94/3.48      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 23.94/3.48      inference(renaming,[status(thm)],[c_89574]) ).
% 23.94/3.48  
% 23.94/3.48  cnf(c_89583,plain,
% 23.94/3.48      ( k3_xboole_0(sK0,sK1) = sK0 ),
% 23.94/3.48      inference(superposition,[status(thm)],[c_11804,c_89575]) ).
% 23.94/3.48  
% 23.94/3.48  cnf(c_6,plain,
% 23.94/3.48      ( k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 23.94/3.48      inference(cnf_transformation,[],[f23]) ).
% 23.94/3.48  
% 23.94/3.48  cnf(c_91722,plain,
% 23.94/3.48      ( k3_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X1)) = k2_zfmisc_1(sK0,k3_xboole_0(X0,X1)) ),
% 23.94/3.48      inference(superposition,[status(thm)],[c_89583,c_6]) ).
% 23.94/3.48  
% 23.94/3.48  cnf(c_7,negated_conjecture,
% 23.94/3.48      ( k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) != k2_zfmisc_1(sK0,sK2) ),
% 23.94/3.48      inference(cnf_transformation,[],[f26]) ).
% 23.94/3.48  
% 23.94/3.48  cnf(c_98457,plain,
% 23.94/3.48      ( k2_zfmisc_1(sK0,k3_xboole_0(sK3,sK2)) != k2_zfmisc_1(sK0,sK2) ),
% 23.94/3.48      inference(demodulation,[status(thm)],[c_91722,c_7]) ).
% 23.94/3.48  
% 23.94/3.48  cnf(c_8,negated_conjecture,
% 23.94/3.48      ( r1_tarski(sK2,sK3) ),
% 23.94/3.48      inference(cnf_transformation,[],[f25]) ).
% 23.94/3.48  
% 23.94/3.48  cnf(c_11805,plain,
% 23.94/3.48      ( r1_tarski(sK2,sK3) = iProver_top ),
% 23.94/3.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 23.94/3.48  
% 23.94/3.48  cnf(c_89582,plain,
% 23.94/3.48      ( k3_xboole_0(sK2,sK3) = sK2 ),
% 23.94/3.48      inference(superposition,[status(thm)],[c_11805,c_89575]) ).
% 23.94/3.48  
% 23.94/3.48  cnf(c_0,plain,
% 23.94/3.48      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 23.94/3.48      inference(cnf_transformation,[],[f17]) ).
% 23.94/3.48  
% 23.94/3.48  cnf(c_90388,plain,
% 23.94/3.48      ( k3_xboole_0(sK3,sK2) = sK2 ),
% 23.94/3.48      inference(superposition,[status(thm)],[c_89582,c_0]) ).
% 23.94/3.48  
% 23.94/3.48  cnf(c_98458,plain,
% 23.94/3.48      ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,sK2) ),
% 23.94/3.48      inference(light_normalisation,[status(thm)],[c_98457,c_90388]) ).
% 23.94/3.48  
% 23.94/3.48  cnf(c_98459,plain,
% 23.94/3.48      ( $false ),
% 23.94/3.48      inference(equality_resolution_simp,[status(thm)],[c_98458]) ).
% 23.94/3.48  
% 23.94/3.48  
% 23.94/3.48  % SZS output end CNFRefutation for theBenchmark.p
% 23.94/3.48  
% 23.94/3.48  ------                               Statistics
% 23.94/3.48  
% 23.94/3.48  ------ Selected
% 23.94/3.48  
% 23.94/3.48  total_time:                             2.974
% 23.94/3.48  
%------------------------------------------------------------------------------
