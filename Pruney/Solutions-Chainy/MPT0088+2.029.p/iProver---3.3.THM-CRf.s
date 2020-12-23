%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:36 EST 2020

% Result     : Theorem 11.93s
% Output     : CNFRefutation 11.93s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 581 expanded)
%              Number of clauses        :   40 ( 185 expanded)
%              Number of leaves         :    8 ( 167 expanded)
%              Depth                    :   17
%              Number of atoms          :   90 ( 672 expanded)
%              Number of equality atoms :   59 ( 568 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :   10 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f15,f20])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).

fof(f24,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f17,f20])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f21,f20,f20])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f16,f20])).

fof(f25,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_48,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_9,negated_conjecture,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_97,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | k4_xboole_0(sK1,sK2) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_48,c_9])).

cnf(c_98,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_97])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_317,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2,c_3])).

cnf(c_5,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_387,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1) ),
    inference(superposition,[status(thm)],[c_317,c_5])).

cnf(c_417,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_387,c_3])).

cnf(c_451,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_98,c_417])).

cnf(c_484,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = sK0 ),
    inference(demodulation,[status(thm)],[c_451,c_3])).

cnf(c_7,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_86,plain,
    ( X0 != X1
    | k4_xboole_0(X2,X0) != X3
    | k4_xboole_0(X3,k4_xboole_0(X3,X1)) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_48,c_7])).

cnf(c_87,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_86])).

cnf(c_450,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_87,c_417])).

cnf(c_487,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_450,c_3])).

cnf(c_523,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X2) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_5,c_487])).

cnf(c_544,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_523,c_5])).

cnf(c_27784,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(sK1,sK2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_484,c_544])).

cnf(c_28404,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(sK1,sK2)) = k4_xboole_0(X0,k4_xboole_0(X0,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_27784,c_484])).

cnf(c_461,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_417,c_5])).

cnf(c_463,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_461,c_5])).

cnf(c_464,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_463,c_5])).

cnf(c_14839,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0))))))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_317,c_464])).

cnf(c_458,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_417,c_87])).

cnf(c_15562,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_14839,c_3,c_317,c_458])).

cnf(c_16853,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_15562,c_5])).

cnf(c_39278,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),sK2) ),
    inference(superposition,[status(thm)],[c_28404,c_16853])).

cnf(c_39321,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_417,c_16853])).

cnf(c_40478,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_39321,c_16853])).

cnf(c_40555,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),sK0) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),sK2) ),
    inference(demodulation,[status(thm)],[c_39278,c_40478])).

cnf(c_40557,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_40555,c_3,c_5,c_317])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_46,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_8,negated_conjecture,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_92,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | k4_xboole_0(sK0,sK2) != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_46,c_8])).

cnf(c_93,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_92])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_40557,c_93])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:18:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 11.93/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.93/2.00  
% 11.93/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.93/2.00  
% 11.93/2.00  ------  iProver source info
% 11.93/2.00  
% 11.93/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.93/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.93/2.00  git: non_committed_changes: false
% 11.93/2.00  git: last_make_outside_of_git: false
% 11.93/2.00  
% 11.93/2.00  ------ 
% 11.93/2.00  ------ Parsing...
% 11.93/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.93/2.00  
% 11.93/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 11.93/2.00  
% 11.93/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.93/2.00  
% 11.93/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.93/2.00  ------ Proving...
% 11.93/2.00  ------ Problem Properties 
% 11.93/2.00  
% 11.93/2.00  
% 11.93/2.00  clauses                                 10
% 11.93/2.00  conjectures                             0
% 11.93/2.00  EPR                                     0
% 11.93/2.00  Horn                                    10
% 11.93/2.00  unary                                   9
% 11.93/2.00  binary                                  1
% 11.93/2.00  lits                                    11
% 11.93/2.00  lits eq                                 11
% 11.93/2.00  fd_pure                                 0
% 11.93/2.00  fd_pseudo                               0
% 11.93/2.00  fd_cond                                 0
% 11.93/2.00  fd_pseudo_cond                          0
% 11.93/2.00  AC symbols                              0
% 11.93/2.00  
% 11.93/2.00  ------ Input Options Time Limit: Unbounded
% 11.93/2.00  
% 11.93/2.00  
% 11.93/2.00  
% 11.93/2.00  
% 11.93/2.00  ------ Preprocessing...
% 11.93/2.00  
% 11.93/2.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 11.93/2.00  Current options:
% 11.93/2.00  ------ 
% 11.93/2.00  
% 11.93/2.00  
% 11.93/2.00  
% 11.93/2.00  
% 11.93/2.00  ------ Proving...
% 11.93/2.00  
% 11.93/2.00  
% 11.93/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.93/2.00  
% 11.93/2.00  ------ Proving...
% 11.93/2.00  
% 11.93/2.00  
% 11.93/2.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.93/2.00  
% 11.93/2.00  ------ Proving...
% 11.93/2.00  
% 11.93/2.00  
% 11.93/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.93/2.00  
% 11.93/2.00  ------ Proving...
% 11.93/2.00  
% 11.93/2.00  
% 11.93/2.00  % SZS status Theorem for theBenchmark.p
% 11.93/2.00  
% 11.93/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.93/2.00  
% 11.93/2.00  fof(f1,axiom,(
% 11.93/2.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 11.93/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.93/2.00  
% 11.93/2.00  fof(f12,plain,(
% 11.93/2.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 11.93/2.00    inference(nnf_transformation,[],[f1])).
% 11.93/2.00  
% 11.93/2.00  fof(f15,plain,(
% 11.93/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 11.93/2.00    inference(cnf_transformation,[],[f12])).
% 11.93/2.00  
% 11.93/2.00  fof(f5,axiom,(
% 11.93/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.93/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.93/2.00  
% 11.93/2.00  fof(f20,plain,(
% 11.93/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.93/2.00    inference(cnf_transformation,[],[f5])).
% 11.93/2.00  
% 11.93/2.00  fof(f27,plain,(
% 11.93/2.00    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 11.93/2.00    inference(definition_unfolding,[],[f15,f20])).
% 11.93/2.00  
% 11.93/2.00  fof(f9,conjecture,(
% 11.93/2.00    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 11.93/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.93/2.00  
% 11.93/2.00  fof(f10,negated_conjecture,(
% 11.93/2.00    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 11.93/2.00    inference(negated_conjecture,[],[f9])).
% 11.93/2.00  
% 11.93/2.00  fof(f11,plain,(
% 11.93/2.00    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 11.93/2.00    inference(ennf_transformation,[],[f10])).
% 11.93/2.00  
% 11.93/2.00  fof(f13,plain,(
% 11.93/2.00    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 11.93/2.00    introduced(choice_axiom,[])).
% 11.93/2.00  
% 11.93/2.00  fof(f14,plain,(
% 11.93/2.00    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 11.93/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).
% 11.93/2.00  
% 11.93/2.00  fof(f24,plain,(
% 11.93/2.00    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 11.93/2.00    inference(cnf_transformation,[],[f14])).
% 11.93/2.00  
% 11.93/2.00  fof(f2,axiom,(
% 11.93/2.00    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 11.93/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.93/2.00  
% 11.93/2.00  fof(f17,plain,(
% 11.93/2.00    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 11.93/2.00    inference(cnf_transformation,[],[f2])).
% 11.93/2.00  
% 11.93/2.00  fof(f28,plain,(
% 11.93/2.00    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 11.93/2.00    inference(definition_unfolding,[],[f17,f20])).
% 11.93/2.00  
% 11.93/2.00  fof(f3,axiom,(
% 11.93/2.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 11.93/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.93/2.00  
% 11.93/2.00  fof(f18,plain,(
% 11.93/2.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.93/2.00    inference(cnf_transformation,[],[f3])).
% 11.93/2.00  
% 11.93/2.00  fof(f6,axiom,(
% 11.93/2.00    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 11.93/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.93/2.00  
% 11.93/2.00  fof(f21,plain,(
% 11.93/2.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 11.93/2.00    inference(cnf_transformation,[],[f6])).
% 11.93/2.00  
% 11.93/2.00  fof(f29,plain,(
% 11.93/2.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 11.93/2.00    inference(definition_unfolding,[],[f21,f20,f20])).
% 11.93/2.00  
% 11.93/2.00  fof(f8,axiom,(
% 11.93/2.00    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 11.93/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.93/2.00  
% 11.93/2.00  fof(f23,plain,(
% 11.93/2.00    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 11.93/2.00    inference(cnf_transformation,[],[f8])).
% 11.93/2.00  
% 11.93/2.00  fof(f16,plain,(
% 11.93/2.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 11.93/2.00    inference(cnf_transformation,[],[f12])).
% 11.93/2.00  
% 11.93/2.00  fof(f26,plain,(
% 11.93/2.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.93/2.00    inference(definition_unfolding,[],[f16,f20])).
% 11.93/2.00  
% 11.93/2.00  fof(f25,plain,(
% 11.93/2.00    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 11.93/2.00    inference(cnf_transformation,[],[f14])).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1,plain,
% 11.93/2.00      ( ~ r1_xboole_0(X0,X1)
% 11.93/2.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.93/2.00      inference(cnf_transformation,[],[f27]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_48,plain,
% 11.93/2.00      ( ~ r1_xboole_0(X0,X1)
% 11.93/2.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.93/2.00      inference(prop_impl,[status(thm)],[c_1]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_9,negated_conjecture,
% 11.93/2.00      ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
% 11.93/2.00      inference(cnf_transformation,[],[f24]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_97,plain,
% 11.93/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 11.93/2.00      | k4_xboole_0(sK1,sK2) != X1
% 11.93/2.00      | sK0 != X0 ),
% 11.93/2.00      inference(resolution_lifted,[status(thm)],[c_48,c_9]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_98,plain,
% 11.93/2.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
% 11.93/2.00      inference(unflattening,[status(thm)],[c_97]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_2,plain,
% 11.93/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 11.93/2.00      inference(cnf_transformation,[],[f28]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_3,plain,
% 11.93/2.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.93/2.00      inference(cnf_transformation,[],[f18]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_317,plain,
% 11.93/2.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.93/2.00      inference(light_normalisation,[status(thm)],[c_2,c_3]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_5,plain,
% 11.93/2.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 11.93/2.00      inference(cnf_transformation,[],[f29]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_387,plain,
% 11.93/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1) ),
% 11.93/2.00      inference(superposition,[status(thm)],[c_317,c_5]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_417,plain,
% 11.93/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 11.93/2.00      inference(light_normalisation,[status(thm)],[c_387,c_3]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_451,plain,
% 11.93/2.00      ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
% 11.93/2.00      inference(superposition,[status(thm)],[c_98,c_417]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_484,plain,
% 11.93/2.00      ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = sK0 ),
% 11.93/2.00      inference(demodulation,[status(thm)],[c_451,c_3]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_7,plain,
% 11.93/2.00      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 11.93/2.00      inference(cnf_transformation,[],[f23]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_86,plain,
% 11.93/2.00      ( X0 != X1
% 11.93/2.00      | k4_xboole_0(X2,X0) != X3
% 11.93/2.00      | k4_xboole_0(X3,k4_xboole_0(X3,X1)) = k1_xboole_0 ),
% 11.93/2.00      inference(resolution_lifted,[status(thm)],[c_48,c_7]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_87,plain,
% 11.93/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
% 11.93/2.00      inference(unflattening,[status(thm)],[c_86]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_450,plain,
% 11.93/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 11.93/2.00      inference(superposition,[status(thm)],[c_87,c_417]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_487,plain,
% 11.93/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 11.93/2.00      inference(demodulation,[status(thm)],[c_450,c_3]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_523,plain,
% 11.93/2.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X2) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 11.93/2.00      inference(superposition,[status(thm)],[c_5,c_487]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_544,plain,
% 11.93/2.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 11.93/2.00      inference(light_normalisation,[status(thm)],[c_523,c_5]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_27784,plain,
% 11.93/2.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(sK1,sK2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) ),
% 11.93/2.00      inference(superposition,[status(thm)],[c_484,c_544]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_28404,plain,
% 11.93/2.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK0)),k4_xboole_0(sK1,sK2)) = k4_xboole_0(X0,k4_xboole_0(X0,sK0)) ),
% 11.93/2.00      inference(light_normalisation,[status(thm)],[c_27784,c_484]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_461,plain,
% 11.93/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 11.93/2.00      inference(superposition,[status(thm)],[c_417,c_5]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_463,plain,
% 11.93/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 11.93/2.00      inference(light_normalisation,[status(thm)],[c_461,c_5]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_464,plain,
% 11.93/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 11.93/2.00      inference(demodulation,[status(thm)],[c_463,c_5]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_14839,plain,
% 11.93/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0))))))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) ),
% 11.93/2.00      inference(superposition,[status(thm)],[c_317,c_464]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_458,plain,
% 11.93/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k1_xboole_0 ),
% 11.93/2.00      inference(superposition,[status(thm)],[c_417,c_87]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_15562,plain,
% 11.93/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
% 11.93/2.00      inference(demodulation,[status(thm)],[c_14839,c_3,c_317,c_458]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_16853,plain,
% 11.93/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 11.93/2.00      inference(superposition,[status(thm)],[c_15562,c_5]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_39278,plain,
% 11.93/2.00      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),sK2) ),
% 11.93/2.00      inference(superposition,[status(thm)],[c_28404,c_16853]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_39321,plain,
% 11.93/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
% 11.93/2.00      inference(superposition,[status(thm)],[c_417,c_16853]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_40478,plain,
% 11.93/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 11.93/2.00      inference(light_normalisation,[status(thm)],[c_39321,c_16853]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_40555,plain,
% 11.93/2.00      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),sK0) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),sK2) ),
% 11.93/2.00      inference(demodulation,[status(thm)],[c_39278,c_40478]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_40557,plain,
% 11.93/2.00      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k1_xboole_0 ),
% 11.93/2.00      inference(demodulation,[status(thm)],[c_40555,c_3,c_5,c_317]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_0,plain,
% 11.93/2.00      ( r1_xboole_0(X0,X1)
% 11.93/2.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 11.93/2.00      inference(cnf_transformation,[],[f26]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_46,plain,
% 11.93/2.00      ( r1_xboole_0(X0,X1)
% 11.93/2.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 11.93/2.00      inference(prop_impl,[status(thm)],[c_0]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_8,negated_conjecture,
% 11.93/2.00      ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
% 11.93/2.00      inference(cnf_transformation,[],[f25]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_92,plain,
% 11.93/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 11.93/2.00      | k4_xboole_0(sK0,sK2) != X1
% 11.93/2.00      | sK1 != X0 ),
% 11.93/2.00      inference(resolution_lifted,[status(thm)],[c_46,c_8]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_93,plain,
% 11.93/2.00      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) != k1_xboole_0 ),
% 11.93/2.00      inference(unflattening,[status(thm)],[c_92]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(contradiction,plain,
% 11.93/2.00      ( $false ),
% 11.93/2.00      inference(minisat,[status(thm)],[c_40557,c_93]) ).
% 11.93/2.00  
% 11.93/2.00  
% 11.93/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.93/2.00  
% 11.93/2.00  ------                               Statistics
% 11.93/2.00  
% 11.93/2.00  ------ Selected
% 11.93/2.00  
% 11.93/2.00  total_time:                             1.253
% 11.93/2.00  
%------------------------------------------------------------------------------
