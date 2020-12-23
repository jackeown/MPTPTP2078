%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:43 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 113 expanded)
%              Number of clauses        :   23 (  40 expanded)
%              Number of leaves         :    8 (  27 expanded)
%              Depth                    :   15
%              Number of atoms          :   70 ( 169 expanded)
%              Number of equality atoms :   40 (  95 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f28,f27,f27])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X2,X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X2,X1))
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).

fof(f30,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f10])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f31,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_7,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_2,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_76,plain,
    ( X0 != X1
    | k4_xboole_0(X0,X2) != X3
    | k4_xboole_0(X3,X1) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_77,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_76])).

cnf(c_360,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_77])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_82,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_10])).

cnf(c_83,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_82])).

cnf(c_353,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X0))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_83,c_7])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_381,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X0))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_353,c_4])).

cnf(c_584,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(X0,sK1))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_360,c_381])).

cnf(c_324,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_77])).

cnf(c_588,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(X0,sK1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_584,c_4,c_324])).

cnf(c_645,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,sK1)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_588,c_381])).

cnf(c_647,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,sK1)) = sK0 ),
    inference(demodulation,[status(thm)],[c_645,c_4])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_9,negated_conjecture,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_70,plain,
    ( k4_xboole_0(X0,X1) != X0
    | k4_xboole_0(sK2,sK1) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_9])).

cnf(c_71,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK2,sK1)) != sK0 ),
    inference(unflattening,[status(thm)],[c_70])).

cnf(c_668,plain,
    ( sK0 != sK0 ),
    inference(demodulation,[status(thm)],[c_647,c_71])).

cnf(c_708,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_668])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 21:05:34 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.79/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/0.99  
% 3.79/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.79/0.99  
% 3.79/0.99  ------  iProver source info
% 3.79/0.99  
% 3.79/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.79/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.79/0.99  git: non_committed_changes: false
% 3.79/0.99  git: last_make_outside_of_git: false
% 3.79/0.99  
% 3.79/0.99  ------ 
% 3.79/0.99  ------ Parsing...
% 3.79/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.79/0.99  ------ Proving...
% 3.79/0.99  ------ Problem Properties 
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  clauses                                 9
% 3.79/0.99  conjectures                             0
% 3.79/0.99  EPR                                     0
% 3.79/0.99  Horn                                    9
% 3.79/0.99  unary                                   9
% 3.79/0.99  binary                                  0
% 3.79/0.99  lits                                    9
% 3.79/0.99  lits eq                                 9
% 3.79/0.99  fd_pure                                 0
% 3.79/0.99  fd_pseudo                               0
% 3.79/0.99  fd_cond                                 0
% 3.79/0.99  fd_pseudo_cond                          0
% 3.79/0.99  AC symbols                              0
% 3.79/0.99  
% 3.79/0.99  ------ Input Options Time Limit: Unbounded
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 3.79/0.99  Current options:
% 3.79/0.99  ------ 
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  ------ Proving...
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.79/0.99  
% 3.79/0.99  ------ Proving...
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.79/0.99  
% 3.79/0.99  ------ Proving...
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.79/0.99  
% 3.79/0.99  ------ Proving...
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.79/0.99  
% 3.79/0.99  ------ Proving...
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  % SZS status Theorem for theBenchmark.p
% 3.79/0.99  
% 3.79/0.99   Resolution empty clause
% 3.79/0.99  
% 3.79/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.79/0.99  
% 3.79/0.99  fof(f9,axiom,(
% 3.79/0.99    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2))),
% 3.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f28,plain,(
% 3.79/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 3.79/0.99    inference(cnf_transformation,[],[f9])).
% 3.79/0.99  
% 3.79/0.99  fof(f8,axiom,(
% 3.79/0.99    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f27,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f8])).
% 3.79/0.99  
% 3.79/0.99  fof(f32,plain,(
% 3.79/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 3.79/0.99    inference(definition_unfolding,[],[f28,f27,f27])).
% 3.79/0.99  
% 3.79/0.99  fof(f2,axiom,(
% 3.79/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f14,plain,(
% 3.79/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 3.79/0.99    inference(unused_predicate_definition_removal,[],[f2])).
% 3.79/0.99  
% 3.79/0.99  fof(f15,plain,(
% 3.79/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 3.79/0.99    inference(ennf_transformation,[],[f14])).
% 3.79/0.99  
% 3.79/0.99  fof(f21,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f15])).
% 3.79/0.99  
% 3.79/0.99  fof(f3,axiom,(
% 3.79/0.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f22,plain,(
% 3.79/0.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f3])).
% 3.79/0.99  
% 3.79/0.99  fof(f11,conjecture,(
% 3.79/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 3.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f12,negated_conjecture,(
% 3.79/0.99    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 3.79/0.99    inference(negated_conjecture,[],[f11])).
% 3.79/0.99  
% 3.79/0.99  fof(f17,plain,(
% 3.79/0.99    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X2,X1)) & r1_tarski(X0,X1))),
% 3.79/0.99    inference(ennf_transformation,[],[f12])).
% 3.79/0.99  
% 3.79/0.99  fof(f18,plain,(
% 3.79/0.99    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X2,X1)) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) & r1_tarski(sK0,sK1))),
% 3.79/0.99    introduced(choice_axiom,[])).
% 3.79/0.99  
% 3.79/0.99  fof(f19,plain,(
% 3.79/0.99    ~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) & r1_tarski(sK0,sK1)),
% 3.79/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).
% 3.79/0.99  
% 3.79/0.99  fof(f30,plain,(
% 3.79/0.99    r1_tarski(sK0,sK1)),
% 3.79/0.99    inference(cnf_transformation,[],[f19])).
% 3.79/0.99  
% 3.79/0.99  fof(f5,axiom,(
% 3.79/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f24,plain,(
% 3.79/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.79/0.99    inference(cnf_transformation,[],[f5])).
% 3.79/0.99  
% 3.79/0.99  fof(f10,axiom,(
% 3.79/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f13,plain,(
% 3.79/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 3.79/0.99    inference(unused_predicate_definition_removal,[],[f10])).
% 3.79/0.99  
% 3.79/0.99  fof(f16,plain,(
% 3.79/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 3.79/0.99    inference(ennf_transformation,[],[f13])).
% 3.79/0.99  
% 3.79/0.99  fof(f29,plain,(
% 3.79/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.79/0.99    inference(cnf_transformation,[],[f16])).
% 3.79/0.99  
% 3.79/0.99  fof(f31,plain,(
% 3.79/0.99    ~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))),
% 3.79/0.99    inference(cnf_transformation,[],[f19])).
% 3.79/0.99  
% 3.79/0.99  cnf(c_7,plain,
% 3.79/0.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 3.79/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_1,plain,
% 3.79/0.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.79/0.99      inference(cnf_transformation,[],[f21]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2,plain,
% 3.79/0.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.79/0.99      inference(cnf_transformation,[],[f22]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_76,plain,
% 3.79/0.99      ( X0 != X1
% 3.79/0.99      | k4_xboole_0(X0,X2) != X3
% 3.79/0.99      | k4_xboole_0(X3,X1) = k1_xboole_0 ),
% 3.79/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_2]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_77,plain,
% 3.79/0.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 3.79/0.99      inference(unflattening,[status(thm)],[c_76]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_360,plain,
% 3.79/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_7,c_77]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_10,negated_conjecture,
% 3.79/0.99      ( r1_tarski(sK0,sK1) ),
% 3.79/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_82,plain,
% 3.79/0.99      ( k4_xboole_0(X0,X1) = k1_xboole_0 | sK1 != X1 | sK0 != X0 ),
% 3.79/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_10]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_83,plain,
% 3.79/0.99      ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
% 3.79/0.99      inference(unflattening,[status(thm)],[c_82]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_353,plain,
% 3.79/0.99      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X0))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0) ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_83,c_7]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4,plain,
% 3.79/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.79/0.99      inference(cnf_transformation,[],[f24]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_381,plain,
% 3.79/0.99      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X0))) = k4_xboole_0(sK0,X0) ),
% 3.79/0.99      inference(demodulation,[status(thm)],[c_353,c_4]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_584,plain,
% 3.79/0.99      ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(X0,sK1))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_360,c_381]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_324,plain,
% 3.79/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_4,c_77]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_588,plain,
% 3.79/0.99      ( k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(X0,sK1))) = k1_xboole_0 ),
% 3.79/0.99      inference(demodulation,[status(thm)],[c_584,c_4,c_324]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_645,plain,
% 3.79/0.99      ( k4_xboole_0(sK0,k4_xboole_0(X0,sK1)) = k4_xboole_0(sK0,k1_xboole_0) ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_588,c_381]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_647,plain,
% 3.79/0.99      ( k4_xboole_0(sK0,k4_xboole_0(X0,sK1)) = sK0 ),
% 3.79/0.99      inference(demodulation,[status(thm)],[c_645,c_4]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_8,plain,
% 3.79/0.99      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 3.79/0.99      inference(cnf_transformation,[],[f29]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_9,negated_conjecture,
% 3.79/0.99      ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
% 3.79/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_70,plain,
% 3.79/0.99      ( k4_xboole_0(X0,X1) != X0 | k4_xboole_0(sK2,sK1) != X1 | sK0 != X0 ),
% 3.79/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_9]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_71,plain,
% 3.79/0.99      ( k4_xboole_0(sK0,k4_xboole_0(sK2,sK1)) != sK0 ),
% 3.79/0.99      inference(unflattening,[status(thm)],[c_70]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_668,plain,
% 3.79/0.99      ( sK0 != sK0 ),
% 3.79/0.99      inference(demodulation,[status(thm)],[c_647,c_71]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_708,plain,
% 3.79/0.99      ( $false ),
% 3.79/0.99      inference(equality_resolution_simp,[status(thm)],[c_668]) ).
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.79/0.99  
% 3.79/0.99  ------                               Statistics
% 3.79/0.99  
% 3.79/0.99  ------ Selected
% 3.79/0.99  
% 3.79/0.99  total_time:                             0.058
% 3.79/0.99  
%------------------------------------------------------------------------------
