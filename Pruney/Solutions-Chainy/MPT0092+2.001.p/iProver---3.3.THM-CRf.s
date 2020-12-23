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
% DateTime   : Thu Dec  3 11:24:43 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :   51 (  93 expanded)
%              Number of clauses        :   24 (  32 expanded)
%              Number of leaves         :    9 (  22 expanded)
%              Depth                    :   14
%              Number of atoms          :   74 ( 142 expanded)
%              Number of equality atoms :   44 (  76 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f30,f29,f29])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X2,X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X2,X1))
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).

fof(f32,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f11])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f33,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_8,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_3,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_78,plain,
    ( X0 != X1
    | k4_xboole_0(X0,X2) != X3
    | k4_xboole_0(X3,X1) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_3])).

cnf(c_79,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_78])).

cnf(c_547,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_79])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_622,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_547,c_7])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_629,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_622,c_5])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_84,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_11])).

cnf(c_85,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_84])).

cnf(c_537,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X0))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_85,c_8])).

cnf(c_576,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X0))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_537,c_5])).

cnf(c_698,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_629,c_576])).

cnf(c_802,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,sK1)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_698,c_85])).

cnf(c_803,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,sK1)) = sK0 ),
    inference(demodulation,[status(thm)],[c_802,c_5])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_10,negated_conjecture,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_72,plain,
    ( k4_xboole_0(X0,X1) != X0
    | k4_xboole_0(sK2,sK1) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_10])).

cnf(c_73,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK2,sK1)) != sK0 ),
    inference(unflattening,[status(thm)],[c_72])).

cnf(c_825,plain,
    ( sK0 != sK0 ),
    inference(demodulation,[status(thm)],[c_803,c_73])).

cnf(c_860,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_825])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:31:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.70/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.03  
% 3.70/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.70/1.03  
% 3.70/1.03  ------  iProver source info
% 3.70/1.03  
% 3.70/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.70/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.70/1.03  git: non_committed_changes: false
% 3.70/1.03  git: last_make_outside_of_git: false
% 3.70/1.03  
% 3.70/1.03  ------ 
% 3.70/1.03  ------ Parsing...
% 3.70/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.70/1.03  
% 3.70/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.70/1.03  
% 3.70/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.70/1.03  
% 3.70/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/1.03  ------ Proving...
% 3.70/1.03  ------ Problem Properties 
% 3.70/1.03  
% 3.70/1.03  
% 3.70/1.03  clauses                                 10
% 3.70/1.03  conjectures                             0
% 3.70/1.03  EPR                                     0
% 3.70/1.03  Horn                                    10
% 3.70/1.03  unary                                   10
% 3.70/1.03  binary                                  0
% 3.70/1.03  lits                                    10
% 3.70/1.03  lits eq                                 10
% 3.70/1.03  fd_pure                                 0
% 3.70/1.03  fd_pseudo                               0
% 3.70/1.03  fd_cond                                 0
% 3.70/1.03  fd_pseudo_cond                          0
% 3.70/1.03  AC symbols                              0
% 3.70/1.03  
% 3.70/1.03  ------ Input Options Time Limit: Unbounded
% 3.70/1.03  
% 3.70/1.03  
% 3.70/1.03  
% 3.70/1.03  
% 3.70/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 3.70/1.03  Current options:
% 3.70/1.03  ------ 
% 3.70/1.03  
% 3.70/1.03  
% 3.70/1.03  
% 3.70/1.03  
% 3.70/1.03  ------ Proving...
% 3.70/1.03  
% 3.70/1.03  
% 3.70/1.03  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/1.03  
% 3.70/1.03  ------ Proving...
% 3.70/1.03  
% 3.70/1.03  
% 3.70/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/1.03  
% 3.70/1.03  ------ Proving...
% 3.70/1.03  
% 3.70/1.03  
% 3.70/1.03  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/1.03  
% 3.70/1.03  ------ Proving...
% 3.70/1.03  
% 3.70/1.03  
% 3.70/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/1.03  
% 3.70/1.03  ------ Proving...
% 3.70/1.03  
% 3.70/1.03  
% 3.70/1.03  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/1.03  
% 3.70/1.03  ------ Proving...
% 3.70/1.03  
% 3.70/1.03  
% 3.70/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.70/1.03  
% 3.70/1.03  ------ Proving...
% 3.70/1.03  
% 3.70/1.03  
% 3.70/1.03  % SZS status Theorem for theBenchmark.p
% 3.70/1.03  
% 3.70/1.03   Resolution empty clause
% 3.70/1.03  
% 3.70/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.70/1.03  
% 3.70/1.03  fof(f10,axiom,(
% 3.70/1.03    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2))),
% 3.70/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.03  
% 3.70/1.03  fof(f30,plain,(
% 3.70/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 3.70/1.03    inference(cnf_transformation,[],[f10])).
% 3.70/1.03  
% 3.70/1.03  fof(f9,axiom,(
% 3.70/1.03    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.70/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.03  
% 3.70/1.03  fof(f29,plain,(
% 3.70/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.70/1.03    inference(cnf_transformation,[],[f9])).
% 3.70/1.03  
% 3.70/1.03  fof(f35,plain,(
% 3.70/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 3.70/1.03    inference(definition_unfolding,[],[f30,f29,f29])).
% 3.70/1.03  
% 3.70/1.03  fof(f2,axiom,(
% 3.70/1.03    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.70/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.03  
% 3.70/1.03  fof(f15,plain,(
% 3.70/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 3.70/1.03    inference(unused_predicate_definition_removal,[],[f2])).
% 3.70/1.03  
% 3.70/1.03  fof(f16,plain,(
% 3.70/1.03    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 3.70/1.03    inference(ennf_transformation,[],[f15])).
% 3.70/1.03  
% 3.70/1.03  fof(f22,plain,(
% 3.70/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.70/1.03    inference(cnf_transformation,[],[f16])).
% 3.70/1.03  
% 3.70/1.03  fof(f4,axiom,(
% 3.70/1.03    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.70/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.03  
% 3.70/1.03  fof(f24,plain,(
% 3.70/1.03    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.70/1.03    inference(cnf_transformation,[],[f4])).
% 3.70/1.03  
% 3.70/1.03  fof(f8,axiom,(
% 3.70/1.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.70/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.03  
% 3.70/1.03  fof(f28,plain,(
% 3.70/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.70/1.03    inference(cnf_transformation,[],[f8])).
% 3.70/1.03  
% 3.70/1.03  fof(f34,plain,(
% 3.70/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.70/1.03    inference(definition_unfolding,[],[f28,f29])).
% 3.70/1.03  
% 3.70/1.03  fof(f6,axiom,(
% 3.70/1.03    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.70/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.03  
% 3.70/1.03  fof(f26,plain,(
% 3.70/1.03    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.70/1.03    inference(cnf_transformation,[],[f6])).
% 3.70/1.03  
% 3.70/1.03  fof(f12,conjecture,(
% 3.70/1.03    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 3.70/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.03  
% 3.70/1.03  fof(f13,negated_conjecture,(
% 3.70/1.03    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 3.70/1.03    inference(negated_conjecture,[],[f12])).
% 3.70/1.03  
% 3.70/1.03  fof(f18,plain,(
% 3.70/1.03    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X2,X1)) & r1_tarski(X0,X1))),
% 3.70/1.03    inference(ennf_transformation,[],[f13])).
% 3.70/1.03  
% 3.70/1.03  fof(f19,plain,(
% 3.70/1.03    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X2,X1)) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) & r1_tarski(sK0,sK1))),
% 3.70/1.03    introduced(choice_axiom,[])).
% 3.70/1.03  
% 3.70/1.03  fof(f20,plain,(
% 3.70/1.03    ~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) & r1_tarski(sK0,sK1)),
% 3.70/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).
% 3.70/1.03  
% 3.70/1.03  fof(f32,plain,(
% 3.70/1.03    r1_tarski(sK0,sK1)),
% 3.70/1.03    inference(cnf_transformation,[],[f20])).
% 3.70/1.03  
% 3.70/1.03  fof(f11,axiom,(
% 3.70/1.03    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.70/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.03  
% 3.70/1.03  fof(f14,plain,(
% 3.70/1.03    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 3.70/1.03    inference(unused_predicate_definition_removal,[],[f11])).
% 3.70/1.03  
% 3.70/1.03  fof(f17,plain,(
% 3.70/1.03    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 3.70/1.03    inference(ennf_transformation,[],[f14])).
% 3.70/1.03  
% 3.70/1.03  fof(f31,plain,(
% 3.70/1.03    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.70/1.03    inference(cnf_transformation,[],[f17])).
% 3.70/1.03  
% 3.70/1.03  fof(f33,plain,(
% 3.70/1.03    ~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))),
% 3.70/1.03    inference(cnf_transformation,[],[f20])).
% 3.70/1.03  
% 3.70/1.03  cnf(c_8,plain,
% 3.70/1.03      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 3.70/1.03      inference(cnf_transformation,[],[f35]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_1,plain,
% 3.70/1.03      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.70/1.03      inference(cnf_transformation,[],[f22]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_3,plain,
% 3.70/1.03      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.70/1.03      inference(cnf_transformation,[],[f24]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_78,plain,
% 3.70/1.03      ( X0 != X1
% 3.70/1.03      | k4_xboole_0(X0,X2) != X3
% 3.70/1.03      | k4_xboole_0(X3,X1) = k1_xboole_0 ),
% 3.70/1.03      inference(resolution_lifted,[status(thm)],[c_1,c_3]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_79,plain,
% 3.70/1.03      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 3.70/1.03      inference(unflattening,[status(thm)],[c_78]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_547,plain,
% 3.70/1.03      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_8,c_79]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_7,plain,
% 3.70/1.03      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.70/1.03      inference(cnf_transformation,[],[f34]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_622,plain,
% 3.70/1.03      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_547,c_7]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_5,plain,
% 3.70/1.03      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.70/1.03      inference(cnf_transformation,[],[f26]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_629,plain,
% 3.70/1.03      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 3.70/1.03      inference(light_normalisation,[status(thm)],[c_622,c_5]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_11,negated_conjecture,
% 3.70/1.03      ( r1_tarski(sK0,sK1) ),
% 3.70/1.03      inference(cnf_transformation,[],[f32]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_84,plain,
% 3.70/1.03      ( k4_xboole_0(X0,X1) = k1_xboole_0 | sK1 != X1 | sK0 != X0 ),
% 3.70/1.03      inference(resolution_lifted,[status(thm)],[c_1,c_11]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_85,plain,
% 3.70/1.03      ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
% 3.70/1.03      inference(unflattening,[status(thm)],[c_84]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_537,plain,
% 3.70/1.03      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X0))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0) ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_85,c_8]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_576,plain,
% 3.70/1.03      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X0))) = k4_xboole_0(sK0,X0) ),
% 3.70/1.03      inference(demodulation,[status(thm)],[c_537,c_5]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_698,plain,
% 3.70/1.03      ( k4_xboole_0(sK0,k4_xboole_0(X0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 3.70/1.03      inference(superposition,[status(thm)],[c_629,c_576]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_802,plain,
% 3.70/1.03      ( k4_xboole_0(sK0,k4_xboole_0(X0,sK1)) = k4_xboole_0(sK0,k1_xboole_0) ),
% 3.70/1.03      inference(light_normalisation,[status(thm)],[c_698,c_85]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_803,plain,
% 3.70/1.03      ( k4_xboole_0(sK0,k4_xboole_0(X0,sK1)) = sK0 ),
% 3.70/1.03      inference(demodulation,[status(thm)],[c_802,c_5]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_9,plain,
% 3.70/1.03      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 3.70/1.03      inference(cnf_transformation,[],[f31]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_10,negated_conjecture,
% 3.70/1.03      ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
% 3.70/1.03      inference(cnf_transformation,[],[f33]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_72,plain,
% 3.70/1.03      ( k4_xboole_0(X0,X1) != X0 | k4_xboole_0(sK2,sK1) != X1 | sK0 != X0 ),
% 3.70/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_10]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_73,plain,
% 3.70/1.03      ( k4_xboole_0(sK0,k4_xboole_0(sK2,sK1)) != sK0 ),
% 3.70/1.03      inference(unflattening,[status(thm)],[c_72]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_825,plain,
% 3.70/1.03      ( sK0 != sK0 ),
% 3.70/1.03      inference(demodulation,[status(thm)],[c_803,c_73]) ).
% 3.70/1.03  
% 3.70/1.03  cnf(c_860,plain,
% 3.70/1.03      ( $false ),
% 3.70/1.03      inference(equality_resolution_simp,[status(thm)],[c_825]) ).
% 3.70/1.03  
% 3.70/1.03  
% 3.70/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.70/1.03  
% 3.70/1.03  ------                               Statistics
% 3.70/1.03  
% 3.70/1.03  ------ Selected
% 3.70/1.03  
% 3.70/1.03  total_time:                             0.108
% 3.70/1.03  
%------------------------------------------------------------------------------
