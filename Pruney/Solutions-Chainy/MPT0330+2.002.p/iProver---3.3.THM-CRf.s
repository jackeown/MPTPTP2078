%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:09 EST 2020

% Result     : Theorem 7.62s
% Output     : CNFRefutation 7.62s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 285 expanded)
%              Number of clauses        :   26 (  52 expanded)
%              Number of leaves         :    8 (  83 expanded)
%              Depth                    :   15
%              Number of atoms          :  104 ( 431 expanded)
%              Number of equality atoms :   47 ( 240 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1))
      & k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f31])).

fof(f46,plain,(
    ! [X2,X0,X1] : k3_tarski(k1_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) = k2_zfmisc_1(k3_tarski(k1_enumset1(X0,X0,X1)),X2) ),
    inference(definition_unfolding,[],[f35,f40,f40])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f30,f31,f31])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f40])).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,(
    ! [X2,X0,X1] : k3_tarski(k1_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(X2,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f36,f40,f40])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f40])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f20,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f21,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f20])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f21,f22])).

fof(f39,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    ~ r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) ),
    inference(definition_unfolding,[],[f39,f40,f40,f40])).

fof(f38,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_10,plain,
    ( k3_tarski(k1_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(k3_tarski(k1_enumset1(X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_6,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2877,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3412,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_2877])).

cnf(c_3465,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(k3_tarski(k1_enumset1(X1,X1,X3)),X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_3412])).

cnf(c_3411,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(k3_tarski(k1_enumset1(X3,X3,X1)),X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_2877])).

cnf(c_9,plain,
    ( k3_tarski(k1_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))) = k2_zfmisc_1(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3464,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X1,k3_tarski(k1_enumset1(X2,X2,X3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_3412])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2875,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2872,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3747,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) != iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2875,c_2872])).

cnf(c_10766,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) != iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3464,c_3747])).

cnf(c_14585,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k1_enumset1(sK3,sK3,sK5)))) != iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3411,c_10766])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_15,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3410,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X1,k3_tarski(k1_enumset1(X3,X3,X2)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_2877])).

cnf(c_14584,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK5)) != iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3410,c_10766])).

cnf(c_19416,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) != iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3411,c_14584])).

cnf(c_21073,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14585,c_15,c_19416])).

cnf(c_21079,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3465,c_21073])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_14,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21079,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:39:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.62/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.62/1.49  
% 7.62/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.62/1.49  
% 7.62/1.49  ------  iProver source info
% 7.62/1.49  
% 7.62/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.62/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.62/1.49  git: non_committed_changes: false
% 7.62/1.49  git: last_make_outside_of_git: false
% 7.62/1.49  
% 7.62/1.49  ------ 
% 7.62/1.49  ------ Parsing...
% 7.62/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.62/1.49  ------ Proving...
% 7.62/1.49  ------ Problem Properties 
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  clauses                                 14
% 7.62/1.49  conjectures                             3
% 7.62/1.49  EPR                                     0
% 7.62/1.49  Horn                                    14
% 7.62/1.49  unary                                   8
% 7.62/1.49  binary                                  5
% 7.62/1.49  lits                                    21
% 7.62/1.49  lits eq                                 5
% 7.62/1.49  fd_pure                                 0
% 7.62/1.49  fd_pseudo                               0
% 7.62/1.49  fd_cond                                 0
% 7.62/1.49  fd_pseudo_cond                          0
% 7.62/1.49  AC symbols                              0
% 7.62/1.49  
% 7.62/1.49  ------ Input Options Time Limit: Unbounded
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing...
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.62/1.49  Current options:
% 7.62/1.49  ------ 
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  ------ Proving...
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing...
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.62/1.49  
% 7.62/1.49  ------ Proving...
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.62/1.49  
% 7.62/1.49  ------ Proving...
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.62/1.49  
% 7.62/1.49  ------ Proving...
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.62/1.49  
% 7.62/1.49  ------ Proving...
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.62/1.49  
% 7.62/1.49  ------ Proving...
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.62/1.49  
% 7.62/1.49  ------ Proving...
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.62/1.49  
% 7.62/1.49  ------ Proving...
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.62/1.49  
% 7.62/1.49  ------ Proving...
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  % SZS status Theorem for theBenchmark.p
% 7.62/1.49  
% 7.62/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.62/1.49  
% 7.62/1.49  fof(f11,axiom,(
% 7.62/1.49    ! [X0,X1,X2] : (k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) & k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2))),
% 7.62/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f35,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f11])).
% 7.62/1.49  
% 7.62/1.49  fof(f9,axiom,(
% 7.62/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.62/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f32,plain,(
% 7.62/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.62/1.49    inference(cnf_transformation,[],[f9])).
% 7.62/1.49  
% 7.62/1.49  fof(f8,axiom,(
% 7.62/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.62/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f31,plain,(
% 7.62/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f8])).
% 7.62/1.49  
% 7.62/1.49  fof(f40,plain,(
% 7.62/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 7.62/1.49    inference(definition_unfolding,[],[f32,f31])).
% 7.62/1.49  
% 7.62/1.49  fof(f46,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (k3_tarski(k1_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) = k2_zfmisc_1(k3_tarski(k1_enumset1(X0,X0,X1)),X2)) )),
% 7.62/1.49    inference(definition_unfolding,[],[f35,f40,f40])).
% 7.62/1.49  
% 7.62/1.49  fof(f7,axiom,(
% 7.62/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.62/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f30,plain,(
% 7.62/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f7])).
% 7.62/1.49  
% 7.62/1.49  fof(f44,plain,(
% 7.62/1.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 7.62/1.49    inference(definition_unfolding,[],[f30,f31,f31])).
% 7.62/1.49  
% 7.62/1.49  fof(f2,axiom,(
% 7.62/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 7.62/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f14,plain,(
% 7.62/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 7.62/1.49    inference(ennf_transformation,[],[f2])).
% 7.62/1.49  
% 7.62/1.49  fof(f25,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f14])).
% 7.62/1.49  
% 7.62/1.49  fof(f41,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 7.62/1.49    inference(definition_unfolding,[],[f25,f40])).
% 7.62/1.49  
% 7.62/1.49  fof(f36,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1))) )),
% 7.62/1.49    inference(cnf_transformation,[],[f11])).
% 7.62/1.49  
% 7.62/1.49  fof(f45,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (k3_tarski(k1_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(X2,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 7.62/1.49    inference(definition_unfolding,[],[f36,f40,f40])).
% 7.62/1.49  
% 7.62/1.49  fof(f6,axiom,(
% 7.62/1.49    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 7.62/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f17,plain,(
% 7.62/1.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 7.62/1.49    inference(ennf_transformation,[],[f6])).
% 7.62/1.49  
% 7.62/1.49  fof(f18,plain,(
% 7.62/1.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 7.62/1.49    inference(flattening,[],[f17])).
% 7.62/1.49  
% 7.62/1.49  fof(f29,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f18])).
% 7.62/1.49  
% 7.62/1.49  fof(f43,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 7.62/1.49    inference(definition_unfolding,[],[f29,f40])).
% 7.62/1.49  
% 7.62/1.49  fof(f12,conjecture,(
% 7.62/1.49    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 7.62/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f13,negated_conjecture,(
% 7.62/1.49    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 7.62/1.49    inference(negated_conjecture,[],[f12])).
% 7.62/1.49  
% 7.62/1.49  fof(f20,plain,(
% 7.62/1.49    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 7.62/1.49    inference(ennf_transformation,[],[f13])).
% 7.62/1.49  
% 7.62/1.49  fof(f21,plain,(
% 7.62/1.49    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 7.62/1.49    inference(flattening,[],[f20])).
% 7.62/1.49  
% 7.62/1.49  fof(f22,plain,(
% 7.62/1.49    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 7.62/1.49    introduced(choice_axiom,[])).
% 7.62/1.49  
% 7.62/1.49  fof(f23,plain,(
% 7.62/1.49    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 7.62/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f21,f22])).
% 7.62/1.49  
% 7.62/1.49  fof(f39,plain,(
% 7.62/1.49    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 7.62/1.49    inference(cnf_transformation,[],[f23])).
% 7.62/1.49  
% 7.62/1.49  fof(f47,plain,(
% 7.62/1.49    ~r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5))))),
% 7.62/1.49    inference(definition_unfolding,[],[f39,f40,f40,f40])).
% 7.62/1.49  
% 7.62/1.49  fof(f38,plain,(
% 7.62/1.49    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 7.62/1.49    inference(cnf_transformation,[],[f23])).
% 7.62/1.49  
% 7.62/1.49  fof(f37,plain,(
% 7.62/1.49    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 7.62/1.49    inference(cnf_transformation,[],[f23])).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10,plain,
% 7.62/1.49      ( k3_tarski(k1_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(k3_tarski(k1_enumset1(X0,X0,X2)),X1) ),
% 7.62/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_6,plain,
% 7.62/1.49      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 7.62/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_1,plain,
% 7.62/1.49      ( ~ r1_tarski(X0,X1)
% 7.62/1.49      | r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
% 7.62/1.49      inference(cnf_transformation,[],[f41]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2877,plain,
% 7.62/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.62/1.49      | r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3412,plain,
% 7.62/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.62/1.49      | r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_6,c_2877]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3465,plain,
% 7.62/1.49      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 7.62/1.49      | r1_tarski(X0,k2_zfmisc_1(k3_tarski(k1_enumset1(X1,X1,X3)),X2)) = iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_10,c_3412]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3411,plain,
% 7.62/1.49      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 7.62/1.49      | r1_tarski(X0,k2_zfmisc_1(k3_tarski(k1_enumset1(X3,X3,X1)),X2)) = iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_10,c_2877]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_9,plain,
% 7.62/1.49      ( k3_tarski(k1_enumset1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))) = k2_zfmisc_1(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ),
% 7.62/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3464,plain,
% 7.62/1.49      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 7.62/1.49      | r1_tarski(X0,k2_zfmisc_1(X1,k3_tarski(k1_enumset1(X2,X2,X3)))) = iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_9,c_3412]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_5,plain,
% 7.62/1.49      ( ~ r1_tarski(X0,X1)
% 7.62/1.49      | ~ r1_tarski(X2,X1)
% 7.62/1.49      | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) ),
% 7.62/1.49      inference(cnf_transformation,[],[f43]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2875,plain,
% 7.62/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.62/1.49      | r1_tarski(X2,X1) != iProver_top
% 7.62/1.49      | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_11,negated_conjecture,
% 7.62/1.49      ( ~ r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) ),
% 7.62/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2872,plain,
% 7.62/1.49      ( r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3747,plain,
% 7.62/1.49      ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) != iProver_top
% 7.62/1.49      | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) != iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_2875,c_2872]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10766,plain,
% 7.62/1.49      ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) != iProver_top
% 7.62/1.49      | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK3)) != iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_3464,c_3747]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_14585,plain,
% 7.62/1.49      ( r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k1_enumset1(sK3,sK3,sK5)))) != iProver_top
% 7.62/1.49      | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK3)) != iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_3411,c_10766]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_12,negated_conjecture,
% 7.62/1.49      ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
% 7.62/1.49      inference(cnf_transformation,[],[f38]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_15,plain,
% 7.62/1.49      ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3410,plain,
% 7.62/1.49      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 7.62/1.49      | r1_tarski(X0,k2_zfmisc_1(X1,k3_tarski(k1_enumset1(X3,X3,X2)))) = iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_9,c_2877]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_14584,plain,
% 7.62/1.49      ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK5)) != iProver_top
% 7.62/1.49      | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK3)) != iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_3410,c_10766]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_19416,plain,
% 7.62/1.49      ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) != iProver_top
% 7.62/1.49      | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK3)) != iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_3411,c_14584]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_21073,plain,
% 7.62/1.49      ( r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK3)) != iProver_top ),
% 7.62/1.49      inference(global_propositional_subsumption,
% 7.62/1.49                [status(thm)],
% 7.62/1.49                [c_14585,c_15,c_19416]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_21079,plain,
% 7.62/1.49      ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) != iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_3465,c_21073]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_13,negated_conjecture,
% 7.62/1.49      ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
% 7.62/1.49      inference(cnf_transformation,[],[f37]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_14,plain,
% 7.62/1.49      ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(contradiction,plain,
% 7.62/1.49      ( $false ),
% 7.62/1.49      inference(minisat,[status(thm)],[c_21079,c_14]) ).
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.62/1.49  
% 7.62/1.49  ------                               Statistics
% 7.62/1.49  
% 7.62/1.49  ------ Selected
% 7.62/1.49  
% 7.62/1.49  total_time:                             0.688
% 7.62/1.49  
%------------------------------------------------------------------------------
