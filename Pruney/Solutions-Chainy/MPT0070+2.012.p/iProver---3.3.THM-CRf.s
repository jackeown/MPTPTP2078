%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:16 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 152 expanded)
%              Number of clauses        :   47 (  61 expanded)
%              Number of leaves         :   15 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  130 ( 242 expanded)
%              Number of equality atoms :   85 ( 141 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,X2)
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    & r1_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).

fof(f33,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f30])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f21,f30,f30])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f25,f30])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f31,f30])).

fof(f32,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f23,f30])).

fof(f34,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_12,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_305,plain,
    ( r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_309,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1652,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_305,c_309])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2048,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1652,c_1])).

cnf(c_7,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_2386,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK1),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2048,c_7])).

cnf(c_6,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_307,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_308,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_802,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_307,c_308])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_321,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5,c_8])).

cnf(c_10,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1070,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_321,c_10])).

cnf(c_1076,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1070,c_8])).

cnf(c_2388,plain,
    ( k4_xboole_0(sK2,sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_2386,c_802,c_1076])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_304,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_803,plain,
    ( k2_xboole_0(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_304,c_308])).

cnf(c_9,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_917,plain,
    ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_307])).

cnf(c_4249,plain,
    ( r1_tarski(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_803,c_917])).

cnf(c_4693,plain,
    ( k2_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK0)) = k4_xboole_0(X0,sK0) ),
    inference(superposition,[status(thm)],[c_4249,c_308])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_923,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9,c_321])).

cnf(c_925,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_923,c_7])).

cnf(c_1655,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_925])).

cnf(c_4948,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4693,c_1655])).

cnf(c_4994,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2388,c_4948])).

cnf(c_104,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_516,plain,
    ( X0 != X1
    | X0 = k4_xboole_0(X2,X3)
    | k4_xboole_0(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_104])).

cnf(c_1013,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_516])).

cnf(c_1014,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1013])).

cnf(c_552,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_454,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != X0
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_104])).

cnf(c_551,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_454])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_374,plain,
    ( r1_xboole_0(sK0,sK2)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_103,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_113,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_103])).

cnf(c_11,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f34])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4994,c_1014,c_552,c_551,c_374,c_113,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : iproveropt_run.sh %d %s
% 0.10/0.31  % Computer   : n009.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % WCLimit    : 600
% 0.10/0.31  % DateTime   : Tue Dec  1 14:16:26 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.16/0.31  % Running in FOF mode
% 3.64/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/0.96  
% 3.64/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.64/0.96  
% 3.64/0.96  ------  iProver source info
% 3.64/0.96  
% 3.64/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.64/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.64/0.96  git: non_committed_changes: false
% 3.64/0.96  git: last_make_outside_of_git: false
% 3.64/0.96  
% 3.64/0.96  ------ 
% 3.64/0.96  ------ Parsing...
% 3.64/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.64/0.96  
% 3.64/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.64/0.96  
% 3.64/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.64/0.96  
% 3.64/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.64/0.96  ------ Proving...
% 3.64/0.96  ------ Problem Properties 
% 3.64/0.96  
% 3.64/0.96  
% 3.64/0.96  clauses                                 14
% 3.64/0.96  conjectures                             3
% 3.64/0.96  EPR                                     3
% 3.64/0.96  Horn                                    14
% 3.64/0.96  unary                                   11
% 3.64/0.96  binary                                  3
% 3.64/0.96  lits                                    17
% 3.64/0.96  lits eq                                 10
% 3.64/0.96  fd_pure                                 0
% 3.64/0.96  fd_pseudo                               0
% 3.64/0.96  fd_cond                                 0
% 3.64/0.96  fd_pseudo_cond                          0
% 3.64/0.96  AC symbols                              0
% 3.64/0.96  
% 3.64/0.96  ------ Input Options Time Limit: Unbounded
% 3.64/0.96  
% 3.64/0.96  
% 3.64/0.96  ------ 
% 3.64/0.96  Current options:
% 3.64/0.96  ------ 
% 3.64/0.96  
% 3.64/0.96  
% 3.64/0.96  
% 3.64/0.96  
% 3.64/0.96  ------ Proving...
% 3.64/0.96  
% 3.64/0.96  
% 3.64/0.96  % SZS status Theorem for theBenchmark.p
% 3.64/0.96  
% 3.64/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 3.64/0.96  
% 3.64/0.96  fof(f12,conjecture,(
% 3.64/0.96    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 3.64/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.96  
% 3.64/0.96  fof(f13,negated_conjecture,(
% 3.64/0.96    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 3.64/0.96    inference(negated_conjecture,[],[f12])).
% 3.64/0.96  
% 3.64/0.96  fof(f15,plain,(
% 3.64/0.96    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & (r1_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 3.64/0.96    inference(ennf_transformation,[],[f13])).
% 3.64/0.96  
% 3.64/0.96  fof(f16,plain,(
% 3.64/0.96    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 3.64/0.96    inference(flattening,[],[f15])).
% 3.64/0.96  
% 3.64/0.96  fof(f18,plain,(
% 3.64/0.96    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 3.64/0.96    introduced(choice_axiom,[])).
% 3.64/0.96  
% 3.64/0.96  fof(f19,plain,(
% 3.64/0.96    ~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 3.64/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).
% 3.64/0.96  
% 3.64/0.96  fof(f33,plain,(
% 3.64/0.96    r1_xboole_0(sK1,sK2)),
% 3.64/0.96    inference(cnf_transformation,[],[f19])).
% 3.64/0.96  
% 3.64/0.96  fof(f3,axiom,(
% 3.64/0.96    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.64/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.96  
% 3.64/0.96  fof(f17,plain,(
% 3.64/0.96    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.64/0.96    inference(nnf_transformation,[],[f3])).
% 3.64/0.96  
% 3.64/0.96  fof(f22,plain,(
% 3.64/0.96    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.64/0.96    inference(cnf_transformation,[],[f17])).
% 3.64/0.96  
% 3.64/0.96  fof(f10,axiom,(
% 3.64/0.96    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.64/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.96  
% 3.64/0.96  fof(f30,plain,(
% 3.64/0.96    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.64/0.96    inference(cnf_transformation,[],[f10])).
% 3.64/0.96  
% 3.64/0.96  fof(f37,plain,(
% 3.64/0.96    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.64/0.96    inference(definition_unfolding,[],[f22,f30])).
% 3.64/0.96  
% 3.64/0.96  fof(f2,axiom,(
% 3.64/0.96    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.64/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.96  
% 3.64/0.96  fof(f21,plain,(
% 3.64/0.96    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.64/0.96    inference(cnf_transformation,[],[f2])).
% 3.64/0.96  
% 3.64/0.96  fof(f35,plain,(
% 3.64/0.96    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.64/0.96    inference(definition_unfolding,[],[f21,f30,f30])).
% 3.64/0.96  
% 3.64/0.96  fof(f7,axiom,(
% 3.64/0.96    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.64/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.96  
% 3.64/0.96  fof(f27,plain,(
% 3.64/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.64/0.96    inference(cnf_transformation,[],[f7])).
% 3.64/0.96  
% 3.64/0.96  fof(f6,axiom,(
% 3.64/0.96    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.64/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.96  
% 3.64/0.96  fof(f26,plain,(
% 3.64/0.96    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.64/0.96    inference(cnf_transformation,[],[f6])).
% 3.64/0.96  
% 3.64/0.96  fof(f4,axiom,(
% 3.64/0.96    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.64/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.96  
% 3.64/0.96  fof(f14,plain,(
% 3.64/0.96    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.64/0.96    inference(ennf_transformation,[],[f4])).
% 3.64/0.96  
% 3.64/0.96  fof(f24,plain,(
% 3.64/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.64/0.96    inference(cnf_transformation,[],[f14])).
% 3.64/0.96  
% 3.64/0.96  fof(f5,axiom,(
% 3.64/0.96    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.64/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.96  
% 3.64/0.96  fof(f25,plain,(
% 3.64/0.96    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.64/0.96    inference(cnf_transformation,[],[f5])).
% 3.64/0.96  
% 3.64/0.96  fof(f38,plain,(
% 3.64/0.96    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 3.64/0.96    inference(definition_unfolding,[],[f25,f30])).
% 3.64/0.96  
% 3.64/0.96  fof(f8,axiom,(
% 3.64/0.96    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.64/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.96  
% 3.64/0.96  fof(f28,plain,(
% 3.64/0.96    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.64/0.96    inference(cnf_transformation,[],[f8])).
% 3.64/0.96  
% 3.64/0.96  fof(f11,axiom,(
% 3.64/0.96    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 3.64/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.96  
% 3.64/0.96  fof(f31,plain,(
% 3.64/0.96    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 3.64/0.96    inference(cnf_transformation,[],[f11])).
% 3.64/0.96  
% 3.64/0.96  fof(f39,plain,(
% 3.64/0.96    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 3.64/0.96    inference(definition_unfolding,[],[f31,f30])).
% 3.64/0.96  
% 3.64/0.96  fof(f32,plain,(
% 3.64/0.96    r1_tarski(sK0,sK1)),
% 3.64/0.96    inference(cnf_transformation,[],[f19])).
% 3.64/0.96  
% 3.64/0.96  fof(f9,axiom,(
% 3.64/0.96    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.64/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.96  
% 3.64/0.96  fof(f29,plain,(
% 3.64/0.96    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.64/0.96    inference(cnf_transformation,[],[f9])).
% 3.64/0.96  
% 3.64/0.96  fof(f1,axiom,(
% 3.64/0.96    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.64/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.96  
% 3.64/0.96  fof(f20,plain,(
% 3.64/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.64/0.96    inference(cnf_transformation,[],[f1])).
% 3.64/0.96  
% 3.64/0.96  fof(f23,plain,(
% 3.64/0.96    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.64/0.96    inference(cnf_transformation,[],[f17])).
% 3.64/0.96  
% 3.64/0.96  fof(f36,plain,(
% 3.64/0.96    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.64/0.96    inference(definition_unfolding,[],[f23,f30])).
% 3.64/0.96  
% 3.64/0.96  fof(f34,plain,(
% 3.64/0.96    ~r1_xboole_0(sK0,sK2)),
% 3.64/0.96    inference(cnf_transformation,[],[f19])).
% 3.64/0.96  
% 3.64/0.96  cnf(c_12,negated_conjecture,
% 3.64/0.96      ( r1_xboole_0(sK1,sK2) ),
% 3.64/0.96      inference(cnf_transformation,[],[f33]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_305,plain,
% 3.64/0.96      ( r1_xboole_0(sK1,sK2) = iProver_top ),
% 3.64/0.96      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_3,plain,
% 3.64/0.96      ( ~ r1_xboole_0(X0,X1)
% 3.64/0.96      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.64/0.96      inference(cnf_transformation,[],[f37]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_309,plain,
% 3.64/0.96      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 3.64/0.96      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.64/0.96      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_1652,plain,
% 3.64/0.96      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 3.64/0.96      inference(superposition,[status(thm)],[c_305,c_309]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_1,plain,
% 3.64/0.96      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.64/0.96      inference(cnf_transformation,[],[f35]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_2048,plain,
% 3.64/0.96      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k1_xboole_0 ),
% 3.64/0.96      inference(superposition,[status(thm)],[c_1652,c_1]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_7,plain,
% 3.64/0.96      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 3.64/0.96      inference(cnf_transformation,[],[f27]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_2386,plain,
% 3.64/0.96      ( k2_xboole_0(k4_xboole_0(sK2,sK1),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK1),k1_xboole_0) ),
% 3.64/0.96      inference(superposition,[status(thm)],[c_2048,c_7]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_6,plain,
% 3.64/0.96      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.64/0.96      inference(cnf_transformation,[],[f26]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_307,plain,
% 3.64/0.96      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 3.64/0.96      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_4,plain,
% 3.64/0.96      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 3.64/0.96      inference(cnf_transformation,[],[f24]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_308,plain,
% 3.64/0.96      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 3.64/0.96      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_802,plain,
% 3.64/0.96      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 3.64/0.96      inference(superposition,[status(thm)],[c_307,c_308]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_5,plain,
% 3.64/0.96      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.64/0.96      inference(cnf_transformation,[],[f38]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_8,plain,
% 3.64/0.96      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.64/0.96      inference(cnf_transformation,[],[f28]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_321,plain,
% 3.64/0.96      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.64/0.96      inference(light_normalisation,[status(thm)],[c_5,c_8]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_10,plain,
% 3.64/0.96      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 3.64/0.96      inference(cnf_transformation,[],[f39]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_1070,plain,
% 3.64/0.96      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
% 3.64/0.96      inference(superposition,[status(thm)],[c_321,c_10]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_1076,plain,
% 3.64/0.96      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.64/0.96      inference(light_normalisation,[status(thm)],[c_1070,c_8]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_2388,plain,
% 3.64/0.96      ( k4_xboole_0(sK2,sK1) = sK2 ),
% 3.64/0.96      inference(demodulation,[status(thm)],[c_2386,c_802,c_1076]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_13,negated_conjecture,
% 3.64/0.96      ( r1_tarski(sK0,sK1) ),
% 3.64/0.96      inference(cnf_transformation,[],[f32]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_304,plain,
% 3.64/0.96      ( r1_tarski(sK0,sK1) = iProver_top ),
% 3.64/0.96      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_803,plain,
% 3.64/0.96      ( k2_xboole_0(sK0,sK1) = sK1 ),
% 3.64/0.96      inference(superposition,[status(thm)],[c_304,c_308]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_9,plain,
% 3.64/0.96      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.64/0.96      inference(cnf_transformation,[],[f29]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_917,plain,
% 3.64/0.96      ( r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = iProver_top ),
% 3.64/0.96      inference(superposition,[status(thm)],[c_9,c_307]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_4249,plain,
% 3.64/0.96      ( r1_tarski(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK0)) = iProver_top ),
% 3.64/0.96      inference(superposition,[status(thm)],[c_803,c_917]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_4693,plain,
% 3.64/0.96      ( k2_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK0)) = k4_xboole_0(X0,sK0) ),
% 3.64/0.96      inference(superposition,[status(thm)],[c_4249,c_308]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_0,plain,
% 3.64/0.96      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 3.64/0.96      inference(cnf_transformation,[],[f20]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_923,plain,
% 3.64/0.96      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 3.64/0.96      inference(superposition,[status(thm)],[c_9,c_321]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_925,plain,
% 3.64/0.96      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 3.64/0.96      inference(demodulation,[status(thm)],[c_923,c_7]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_1655,plain,
% 3.64/0.96      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.64/0.96      inference(superposition,[status(thm)],[c_0,c_925]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_4948,plain,
% 3.64/0.96      ( k4_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK0)) = k1_xboole_0 ),
% 3.64/0.96      inference(superposition,[status(thm)],[c_4693,c_1655]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_4994,plain,
% 3.64/0.96      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
% 3.64/0.96      inference(superposition,[status(thm)],[c_2388,c_4948]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_104,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_516,plain,
% 3.64/0.96      ( X0 != X1 | X0 = k4_xboole_0(X2,X3) | k4_xboole_0(X2,X3) != X1 ),
% 3.64/0.96      inference(instantiation,[status(thm)],[c_104]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_1013,plain,
% 3.64/0.96      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) != X0
% 3.64/0.96      | k1_xboole_0 != X0
% 3.64/0.96      | k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
% 3.64/0.96      inference(instantiation,[status(thm)],[c_516]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_1014,plain,
% 3.64/0.96      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) != k1_xboole_0
% 3.64/0.96      | k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))
% 3.64/0.96      | k1_xboole_0 != k1_xboole_0 ),
% 3.64/0.96      inference(instantiation,[status(thm)],[c_1013]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_552,plain,
% 3.64/0.96      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
% 3.64/0.96      inference(instantiation,[status(thm)],[c_1]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_454,plain,
% 3.64/0.96      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != X0
% 3.64/0.96      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
% 3.64/0.96      | k1_xboole_0 != X0 ),
% 3.64/0.96      inference(instantiation,[status(thm)],[c_104]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_551,plain,
% 3.64/0.96      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))
% 3.64/0.96      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0
% 3.64/0.96      | k1_xboole_0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
% 3.64/0.96      inference(instantiation,[status(thm)],[c_454]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_2,plain,
% 3.64/0.96      ( r1_xboole_0(X0,X1)
% 3.64/0.96      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 3.64/0.96      inference(cnf_transformation,[],[f36]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_374,plain,
% 3.64/0.96      ( r1_xboole_0(sK0,sK2)
% 3.64/0.96      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k1_xboole_0 ),
% 3.64/0.96      inference(instantiation,[status(thm)],[c_2]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_103,plain,( X0 = X0 ),theory(equality) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_113,plain,
% 3.64/0.96      ( k1_xboole_0 = k1_xboole_0 ),
% 3.64/0.96      inference(instantiation,[status(thm)],[c_103]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(c_11,negated_conjecture,
% 3.64/0.96      ( ~ r1_xboole_0(sK0,sK2) ),
% 3.64/0.96      inference(cnf_transformation,[],[f34]) ).
% 3.64/0.96  
% 3.64/0.96  cnf(contradiction,plain,
% 3.64/0.96      ( $false ),
% 3.64/0.96      inference(minisat,
% 3.64/0.96                [status(thm)],
% 3.64/0.96                [c_4994,c_1014,c_552,c_551,c_374,c_113,c_11]) ).
% 3.64/0.96  
% 3.64/0.96  
% 3.64/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 3.64/0.96  
% 3.64/0.96  ------                               Statistics
% 3.64/0.96  
% 3.64/0.96  ------ Selected
% 3.64/0.96  
% 3.64/0.96  total_time:                             0.178
% 3.64/0.96  
%------------------------------------------------------------------------------
