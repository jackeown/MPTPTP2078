%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:44 EST 2020

% Result     : Theorem 11.86s
% Output     : CNFRefutation 11.86s
% Verified   : 
% Statistics : Number of formulae       :   41 (  46 expanded)
%              Number of clauses        :   19 (  19 expanded)
%              Number of leaves         :    8 (  10 expanded)
%              Depth                    :   12
%              Number of atoms          :   60 (  72 expanded)
%              Number of equality atoms :   27 (  27 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X2,X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X2,X1))
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f21,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f22,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_7,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_64,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_7])).

cnf(c_65,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_64])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_4088,plain,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_65,c_3])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_4089,plain,
    ( k2_xboole_0(sK1,sK0) = sK1 ),
    inference(demodulation,[status(thm)],[c_4088,c_2])).

cnf(c_4,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_5,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_4043,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4100,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_4043])).

cnf(c_4168,plain,
    ( r1_xboole_0(k4_xboole_0(X0,sK1),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4089,c_4100])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_4044,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4862,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(X0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4168,c_4044])).

cnf(c_6,negated_conjecture,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_4042,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_48433,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_4862,c_4042])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:45:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 11.86/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.86/2.00  
% 11.86/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.86/2.00  
% 11.86/2.00  ------  iProver source info
% 11.86/2.00  
% 11.86/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.86/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.86/2.00  git: non_committed_changes: false
% 11.86/2.00  git: last_make_outside_of_git: false
% 11.86/2.00  
% 11.86/2.00  ------ 
% 11.86/2.00  ------ Parsing...
% 11.86/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.86/2.00  ------ Proving...
% 11.86/2.00  ------ Problem Properties 
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  clauses                                 7
% 11.86/2.00  conjectures                             1
% 11.86/2.00  EPR                                     1
% 11.86/2.00  Horn                                    7
% 11.86/2.00  unary                                   6
% 11.86/2.00  binary                                  1
% 11.86/2.00  lits                                    8
% 11.86/2.00  lits eq                                 4
% 11.86/2.00  fd_pure                                 0
% 11.86/2.00  fd_pseudo                               0
% 11.86/2.00  fd_cond                                 0
% 11.86/2.00  fd_pseudo_cond                          0
% 11.86/2.00  AC symbols                              0
% 11.86/2.00  
% 11.86/2.00  ------ Input Options Time Limit: Unbounded
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing...
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 11.86/2.00  Current options:
% 11.86/2.00  ------ 
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  ------ Proving...
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.86/2.00  
% 11.86/2.00  ------ Proving...
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.86/2.00  
% 11.86/2.00  ------ Proving...
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.86/2.00  
% 11.86/2.00  ------ Proving...
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.86/2.00  
% 11.86/2.00  ------ Proving...
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.86/2.00  
% 11.86/2.00  ------ Proving...
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing...
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.86/2.00  
% 11.86/2.00  ------ Proving...
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.86/2.00  
% 11.86/2.00  ------ Proving...
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.86/2.00  
% 11.86/2.00  ------ Proving...
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.86/2.00  
% 11.86/2.00  ------ Proving...
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.86/2.00  
% 11.86/2.00  ------ Proving...
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.86/2.00  
% 11.86/2.00  ------ Proving...
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing...
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.86/2.00  
% 11.86/2.00  ------ Proving...
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.86/2.00  
% 11.86/2.00  ------ Proving...
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.86/2.00  
% 11.86/2.00  ------ Proving...
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.86/2.00  
% 11.86/2.00  ------ Proving...
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.86/2.00  
% 11.86/2.00  ------ Proving...
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.86/2.00  
% 11.86/2.00  ------ Proving...
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.86/2.00  
% 11.86/2.00  ------ Proving...
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.86/2.00  
% 11.86/2.00  ------ Proving...
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  % SZS status Theorem for theBenchmark.p
% 11.86/2.00  
% 11.86/2.00   Resolution empty clause
% 11.86/2.00  
% 11.86/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.86/2.00  
% 11.86/2.00  fof(f2,axiom,(
% 11.86/2.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 11.86/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f9,plain,(
% 11.86/2.00    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 11.86/2.00    inference(unused_predicate_definition_removal,[],[f2])).
% 11.86/2.00  
% 11.86/2.00  fof(f11,plain,(
% 11.86/2.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 11.86/2.00    inference(ennf_transformation,[],[f9])).
% 11.86/2.00  
% 11.86/2.00  fof(f16,plain,(
% 11.86/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f11])).
% 11.86/2.00  
% 11.86/2.00  fof(f7,conjecture,(
% 11.86/2.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 11.86/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f8,negated_conjecture,(
% 11.86/2.00    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 11.86/2.00    inference(negated_conjecture,[],[f7])).
% 11.86/2.00  
% 11.86/2.00  fof(f12,plain,(
% 11.86/2.00    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X2,X1)) & r1_tarski(X0,X1))),
% 11.86/2.00    inference(ennf_transformation,[],[f8])).
% 11.86/2.00  
% 11.86/2.00  fof(f13,plain,(
% 11.86/2.00    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X2,X1)) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) & r1_tarski(sK0,sK1))),
% 11.86/2.00    introduced(choice_axiom,[])).
% 11.86/2.00  
% 11.86/2.00  fof(f14,plain,(
% 11.86/2.00    ~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) & r1_tarski(sK0,sK1)),
% 11.86/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 11.86/2.00  
% 11.86/2.00  fof(f21,plain,(
% 11.86/2.00    r1_tarski(sK0,sK1)),
% 11.86/2.00    inference(cnf_transformation,[],[f14])).
% 11.86/2.00  
% 11.86/2.00  fof(f4,axiom,(
% 11.86/2.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 11.86/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f18,plain,(
% 11.86/2.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 11.86/2.00    inference(cnf_transformation,[],[f4])).
% 11.86/2.00  
% 11.86/2.00  fof(f3,axiom,(
% 11.86/2.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 11.86/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f17,plain,(
% 11.86/2.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.86/2.00    inference(cnf_transformation,[],[f3])).
% 11.86/2.00  
% 11.86/2.00  fof(f5,axiom,(
% 11.86/2.00    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 11.86/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f19,plain,(
% 11.86/2.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f5])).
% 11.86/2.00  
% 11.86/2.00  fof(f6,axiom,(
% 11.86/2.00    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 11.86/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f20,plain,(
% 11.86/2.00    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f6])).
% 11.86/2.00  
% 11.86/2.00  fof(f1,axiom,(
% 11.86/2.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 11.86/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f10,plain,(
% 11.86/2.00    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 11.86/2.00    inference(ennf_transformation,[],[f1])).
% 11.86/2.00  
% 11.86/2.00  fof(f15,plain,(
% 11.86/2.00    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f10])).
% 11.86/2.00  
% 11.86/2.00  fof(f22,plain,(
% 11.86/2.00    ~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))),
% 11.86/2.00    inference(cnf_transformation,[],[f14])).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1,plain,
% 11.86/2.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 11.86/2.00      inference(cnf_transformation,[],[f16]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_7,negated_conjecture,
% 11.86/2.00      ( r1_tarski(sK0,sK1) ),
% 11.86/2.00      inference(cnf_transformation,[],[f21]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_64,plain,
% 11.86/2.00      ( k4_xboole_0(X0,X1) = k1_xboole_0 | sK1 != X1 | sK0 != X0 ),
% 11.86/2.00      inference(resolution_lifted,[status(thm)],[c_1,c_7]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_65,plain,
% 11.86/2.00      ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
% 11.86/2.00      inference(unflattening,[status(thm)],[c_64]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_3,plain,
% 11.86/2.00      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.86/2.00      inference(cnf_transformation,[],[f18]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_4088,plain,
% 11.86/2.00      ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0) ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_65,c_3]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_2,plain,
% 11.86/2.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.86/2.00      inference(cnf_transformation,[],[f17]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_4089,plain,
% 11.86/2.00      ( k2_xboole_0(sK1,sK0) = sK1 ),
% 11.86/2.00      inference(demodulation,[status(thm)],[c_4088,c_2]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_4,plain,
% 11.86/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.86/2.00      inference(cnf_transformation,[],[f19]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_5,plain,
% 11.86/2.00      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 11.86/2.00      inference(cnf_transformation,[],[f20]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_4043,plain,
% 11.86/2.00      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_4100,plain,
% 11.86/2.00      ( r1_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_4,c_4043]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_4168,plain,
% 11.86/2.00      ( r1_xboole_0(k4_xboole_0(X0,sK1),sK0) = iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_4089,c_4100]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_0,plain,
% 11.86/2.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 11.86/2.00      inference(cnf_transformation,[],[f15]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_4044,plain,
% 11.86/2.00      ( r1_xboole_0(X0,X1) != iProver_top | r1_xboole_0(X1,X0) = iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_4862,plain,
% 11.86/2.00      ( r1_xboole_0(sK0,k4_xboole_0(X0,sK1)) = iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_4168,c_4044]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_6,negated_conjecture,
% 11.86/2.00      ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
% 11.86/2.00      inference(cnf_transformation,[],[f22]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_4042,plain,
% 11.86/2.00      ( r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_48433,plain,
% 11.86/2.00      ( $false ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_4862,c_4042]) ).
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.86/2.00  
% 11.86/2.00  ------                               Statistics
% 11.86/2.00  
% 11.86/2.00  ------ Selected
% 11.86/2.00  
% 11.86/2.00  total_time:                             1.302
% 11.86/2.00  
%------------------------------------------------------------------------------
