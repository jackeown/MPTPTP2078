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
% DateTime   : Thu Dec  3 11:24:35 EST 2020

% Result     : Theorem 31.71s
% Output     : CNFRefutation 31.71s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 222 expanded)
%              Number of clauses        :   34 (  77 expanded)
%              Number of leaves         :    9 (  57 expanded)
%              Depth                    :   16
%              Number of atoms          :   93 ( 298 expanded)
%              Number of equality atoms :   57 ( 207 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f19,f28])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).

fof(f30,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f27,f28])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f29,f28,f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f20,f28])).

fof(f31,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_59,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_11,negated_conjecture,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_116,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | k4_xboole_0(sK1,sK2) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_59,c_11])).

cnf(c_117,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_116])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_37200,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_117,c_8])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_37225,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = sK0 ),
    inference(demodulation,[status(thm)],[c_37200,c_5])).

cnf(c_9,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_3,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_103,plain,
    ( X0 != X1
    | k4_xboole_0(X0,X2) != X3
    | k4_xboole_0(X3,X1) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_3])).

cnf(c_104,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_103])).

cnf(c_37254,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9,c_104])).

cnf(c_37352,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_37254,c_8])).

cnf(c_37362,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_37352,c_5])).

cnf(c_37376,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_9,c_37362])).

cnf(c_37449,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X0,k4_xboole_0(X0,sK0))) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_37225,c_37376])).

cnf(c_37608,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(sK1,sK2)) = k4_xboole_0(X0,k4_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_37449,c_37362])).

cnf(c_37243,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),X2) ),
    inference(superposition,[status(thm)],[c_104,c_9])).

cnf(c_37286,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_37243,c_5])).

cnf(c_56281,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),sK2) ),
    inference(superposition,[status(thm)],[c_37608,c_37286])).

cnf(c_56359,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_8,c_37286])).

cnf(c_56858,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_56359,c_37286])).

cnf(c_56958,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),sK0) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),sK2) ),
    inference(demodulation,[status(thm)],[c_56281,c_56858])).

cnf(c_37178,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_104])).

cnf(c_56960,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_56958,c_5,c_9,c_37178])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_57,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_10,negated_conjecture,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_111,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | k4_xboole_0(sK0,sK2) != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_57,c_10])).

cnf(c_112,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_111])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_56960,c_112])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:16:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 31.71/4.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.71/4.50  
% 31.71/4.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.71/4.50  
% 31.71/4.50  ------  iProver source info
% 31.71/4.50  
% 31.71/4.50  git: date: 2020-06-30 10:37:57 +0100
% 31.71/4.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.71/4.50  git: non_committed_changes: false
% 31.71/4.50  git: last_make_outside_of_git: false
% 31.71/4.50  
% 31.71/4.50  ------ 
% 31.71/4.50  ------ Parsing...
% 31.71/4.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.71/4.50  
% 31.71/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 31.71/4.50  
% 31.71/4.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.71/4.50  
% 31.71/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.71/4.50  ------ Proving...
% 31.71/4.50  ------ Problem Properties 
% 31.71/4.50  
% 31.71/4.50  
% 31.71/4.50  clauses                                 10
% 31.71/4.50  conjectures                             0
% 31.71/4.50  EPR                                     0
% 31.71/4.50  Horn                                    10
% 31.71/4.50  unary                                   9
% 31.71/4.50  binary                                  1
% 31.71/4.50  lits                                    11
% 31.71/4.50  lits eq                                 11
% 31.71/4.50  fd_pure                                 0
% 31.71/4.50  fd_pseudo                               0
% 31.71/4.50  fd_cond                                 0
% 31.71/4.50  fd_pseudo_cond                          0
% 31.71/4.50  AC symbols                              0
% 31.71/4.50  
% 31.71/4.50  ------ Input Options Time Limit: Unbounded
% 31.71/4.50  
% 31.71/4.50  
% 31.71/4.50  
% 31.71/4.50  
% 31.71/4.50  ------ Preprocessing...
% 31.71/4.50  
% 31.71/4.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 31.71/4.50  Current options:
% 31.71/4.50  ------ 
% 31.71/4.50  
% 31.71/4.50  
% 31.71/4.50  
% 31.71/4.50  
% 31.71/4.50  ------ Proving...
% 31.71/4.50  
% 31.71/4.50  
% 31.71/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.71/4.50  
% 31.71/4.50  ------ Proving...
% 31.71/4.50  
% 31.71/4.50  
% 31.71/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.71/4.50  
% 31.71/4.50  ------ Proving...
% 31.71/4.50  
% 31.71/4.50  
% 31.71/4.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.71/4.50  
% 31.71/4.50  ------ Proving...
% 31.71/4.50  
% 31.71/4.50  
% 31.71/4.50  % SZS status Theorem for theBenchmark.p
% 31.71/4.50  
% 31.71/4.50  % SZS output start CNFRefutation for theBenchmark.p
% 31.71/4.50  
% 31.71/4.50  fof(f1,axiom,(
% 31.71/4.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 31.71/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.71/4.50  
% 31.71/4.50  fof(f16,plain,(
% 31.71/4.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 31.71/4.50    inference(nnf_transformation,[],[f1])).
% 31.71/4.50  
% 31.71/4.50  fof(f19,plain,(
% 31.71/4.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 31.71/4.50    inference(cnf_transformation,[],[f16])).
% 31.71/4.50  
% 31.71/4.50  fof(f9,axiom,(
% 31.71/4.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 31.71/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.71/4.50  
% 31.71/4.50  fof(f28,plain,(
% 31.71/4.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 31.71/4.50    inference(cnf_transformation,[],[f9])).
% 31.71/4.50  
% 31.71/4.50  fof(f33,plain,(
% 31.71/4.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 31.71/4.50    inference(definition_unfolding,[],[f19,f28])).
% 31.71/4.50  
% 31.71/4.50  fof(f11,conjecture,(
% 31.71/4.50    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 31.71/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.71/4.50  
% 31.71/4.50  fof(f12,negated_conjecture,(
% 31.71/4.50    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 31.71/4.50    inference(negated_conjecture,[],[f11])).
% 31.71/4.50  
% 31.71/4.50  fof(f15,plain,(
% 31.71/4.50    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 31.71/4.50    inference(ennf_transformation,[],[f12])).
% 31.71/4.50  
% 31.71/4.50  fof(f17,plain,(
% 31.71/4.50    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 31.71/4.50    introduced(choice_axiom,[])).
% 31.71/4.50  
% 31.71/4.50  fof(f18,plain,(
% 31.71/4.50    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 31.71/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).
% 31.71/4.50  
% 31.71/4.50  fof(f30,plain,(
% 31.71/4.50    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 31.71/4.50    inference(cnf_transformation,[],[f18])).
% 31.71/4.50  
% 31.71/4.50  fof(f8,axiom,(
% 31.71/4.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 31.71/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.71/4.50  
% 31.71/4.50  fof(f27,plain,(
% 31.71/4.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 31.71/4.50    inference(cnf_transformation,[],[f8])).
% 31.71/4.50  
% 31.71/4.50  fof(f34,plain,(
% 31.71/4.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 31.71/4.50    inference(definition_unfolding,[],[f27,f28])).
% 31.71/4.50  
% 31.71/4.50  fof(f5,axiom,(
% 31.71/4.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 31.71/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.71/4.50  
% 31.71/4.50  fof(f24,plain,(
% 31.71/4.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 31.71/4.50    inference(cnf_transformation,[],[f5])).
% 31.71/4.50  
% 31.71/4.50  fof(f10,axiom,(
% 31.71/4.50    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 31.71/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.71/4.50  
% 31.71/4.50  fof(f29,plain,(
% 31.71/4.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 31.71/4.50    inference(cnf_transformation,[],[f10])).
% 31.71/4.50  
% 31.71/4.50  fof(f35,plain,(
% 31.71/4.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 31.71/4.50    inference(definition_unfolding,[],[f29,f28,f28])).
% 31.71/4.50  
% 31.71/4.50  fof(f2,axiom,(
% 31.71/4.50    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 31.71/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.71/4.50  
% 31.71/4.50  fof(f13,plain,(
% 31.71/4.50    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 31.71/4.50    inference(unused_predicate_definition_removal,[],[f2])).
% 31.71/4.50  
% 31.71/4.50  fof(f14,plain,(
% 31.71/4.50    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 31.71/4.50    inference(ennf_transformation,[],[f13])).
% 31.71/4.50  
% 31.71/4.50  fof(f21,plain,(
% 31.71/4.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 31.71/4.50    inference(cnf_transformation,[],[f14])).
% 31.71/4.50  
% 31.71/4.50  fof(f3,axiom,(
% 31.71/4.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 31.71/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.71/4.50  
% 31.71/4.50  fof(f22,plain,(
% 31.71/4.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 31.71/4.50    inference(cnf_transformation,[],[f3])).
% 31.71/4.50  
% 31.71/4.50  fof(f20,plain,(
% 31.71/4.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 31.71/4.50    inference(cnf_transformation,[],[f16])).
% 31.71/4.50  
% 31.71/4.50  fof(f32,plain,(
% 31.71/4.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 31.71/4.50    inference(definition_unfolding,[],[f20,f28])).
% 31.71/4.50  
% 31.71/4.50  fof(f31,plain,(
% 31.71/4.50    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 31.71/4.50    inference(cnf_transformation,[],[f18])).
% 31.71/4.50  
% 31.71/4.50  cnf(c_1,plain,
% 31.71/4.50      ( ~ r1_xboole_0(X0,X1)
% 31.71/4.50      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 31.71/4.50      inference(cnf_transformation,[],[f33]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_59,plain,
% 31.71/4.50      ( ~ r1_xboole_0(X0,X1)
% 31.71/4.50      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 31.71/4.50      inference(prop_impl,[status(thm)],[c_1]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_11,negated_conjecture,
% 31.71/4.50      ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
% 31.71/4.50      inference(cnf_transformation,[],[f30]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_116,plain,
% 31.71/4.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 31.71/4.50      | k4_xboole_0(sK1,sK2) != X1
% 31.71/4.50      | sK0 != X0 ),
% 31.71/4.50      inference(resolution_lifted,[status(thm)],[c_59,c_11]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_117,plain,
% 31.71/4.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
% 31.71/4.50      inference(unflattening,[status(thm)],[c_116]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_8,plain,
% 31.71/4.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 31.71/4.50      inference(cnf_transformation,[],[f34]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_37200,plain,
% 31.71/4.50      ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
% 31.71/4.50      inference(superposition,[status(thm)],[c_117,c_8]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_5,plain,
% 31.71/4.50      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 31.71/4.50      inference(cnf_transformation,[],[f24]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_37225,plain,
% 31.71/4.50      ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = sK0 ),
% 31.71/4.50      inference(demodulation,[status(thm)],[c_37200,c_5]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_9,plain,
% 31.71/4.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 31.71/4.50      inference(cnf_transformation,[],[f35]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_2,plain,
% 31.71/4.50      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 31.71/4.50      inference(cnf_transformation,[],[f21]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_3,plain,
% 31.71/4.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 31.71/4.50      inference(cnf_transformation,[],[f22]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_103,plain,
% 31.71/4.50      ( X0 != X1
% 31.71/4.50      | k4_xboole_0(X0,X2) != X3
% 31.71/4.50      | k4_xboole_0(X3,X1) = k1_xboole_0 ),
% 31.71/4.50      inference(resolution_lifted,[status(thm)],[c_2,c_3]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_104,plain,
% 31.71/4.50      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 31.71/4.50      inference(unflattening,[status(thm)],[c_103]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_37254,plain,
% 31.71/4.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 31.71/4.50      inference(superposition,[status(thm)],[c_9,c_104]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_37352,plain,
% 31.71/4.50      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 31.71/4.50      inference(superposition,[status(thm)],[c_37254,c_8]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_37362,plain,
% 31.71/4.50      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 31.71/4.50      inference(light_normalisation,[status(thm)],[c_37352,c_5]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_37376,plain,
% 31.71/4.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0)))) = X0 ),
% 31.71/4.50      inference(superposition,[status(thm)],[c_9,c_37362]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_37449,plain,
% 31.71/4.50      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X0,k4_xboole_0(X0,sK0))) = k4_xboole_0(sK1,sK2) ),
% 31.71/4.50      inference(superposition,[status(thm)],[c_37225,c_37376]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_37608,plain,
% 31.71/4.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(sK1,sK2)) = k4_xboole_0(X0,k4_xboole_0(X0,sK0)) ),
% 31.71/4.50      inference(superposition,[status(thm)],[c_37449,c_37362]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_37243,plain,
% 31.71/4.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),X2) ),
% 31.71/4.50      inference(superposition,[status(thm)],[c_104,c_9]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_37286,plain,
% 31.71/4.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 31.71/4.50      inference(demodulation,[status(thm)],[c_37243,c_5]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_56281,plain,
% 31.71/4.50      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),sK2) ),
% 31.71/4.50      inference(superposition,[status(thm)],[c_37608,c_37286]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_56359,plain,
% 31.71/4.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
% 31.71/4.50      inference(superposition,[status(thm)],[c_8,c_37286]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_56858,plain,
% 31.71/4.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 31.71/4.50      inference(light_normalisation,[status(thm)],[c_56359,c_37286]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_56958,plain,
% 31.71/4.50      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),sK0) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),sK2) ),
% 31.71/4.50      inference(demodulation,[status(thm)],[c_56281,c_56858]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_37178,plain,
% 31.71/4.50      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 31.71/4.50      inference(superposition,[status(thm)],[c_5,c_104]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_56960,plain,
% 31.71/4.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k1_xboole_0 ),
% 31.71/4.50      inference(demodulation,[status(thm)],[c_56958,c_5,c_9,c_37178]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_0,plain,
% 31.71/4.50      ( r1_xboole_0(X0,X1)
% 31.71/4.50      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 31.71/4.50      inference(cnf_transformation,[],[f32]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_57,plain,
% 31.71/4.50      ( r1_xboole_0(X0,X1)
% 31.71/4.50      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 31.71/4.50      inference(prop_impl,[status(thm)],[c_0]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_10,negated_conjecture,
% 31.71/4.50      ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
% 31.71/4.50      inference(cnf_transformation,[],[f31]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_111,plain,
% 31.71/4.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 31.71/4.50      | k4_xboole_0(sK0,sK2) != X1
% 31.71/4.50      | sK1 != X0 ),
% 31.71/4.50      inference(resolution_lifted,[status(thm)],[c_57,c_10]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(c_112,plain,
% 31.71/4.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) != k1_xboole_0 ),
% 31.71/4.50      inference(unflattening,[status(thm)],[c_111]) ).
% 31.71/4.50  
% 31.71/4.50  cnf(contradiction,plain,
% 31.71/4.50      ( $false ),
% 31.71/4.50      inference(minisat,[status(thm)],[c_56960,c_112]) ).
% 31.71/4.50  
% 31.71/4.50  
% 31.71/4.50  % SZS output end CNFRefutation for theBenchmark.p
% 31.71/4.50  
% 31.71/4.50  ------                               Statistics
% 31.71/4.50  
% 31.71/4.50  ------ Selected
% 31.71/4.50  
% 31.71/4.50  total_time:                             3.663
% 31.71/4.50  
%------------------------------------------------------------------------------
