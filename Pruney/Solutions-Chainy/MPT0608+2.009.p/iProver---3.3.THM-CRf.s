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
% DateTime   : Thu Dec  3 11:48:41 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   52 (  73 expanded)
%              Number of clauses        :   24 (  28 expanded)
%              Number of leaves         :    9 (  15 expanded)
%              Depth                    :   11
%              Number of atoms          :  103 ( 145 expanded)
%              Number of equality atoms :   53 (  73 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))
        & v1_relat_1(X1) )
   => ( k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f17])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f15])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f28,plain,(
    k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_8,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_252,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_257,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k6_subset_1(X0,X2),X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_256,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k6_subset_1(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_254,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_742,plain,
    ( k1_relat_1(k7_relat_1(X0,k6_subset_1(X1,X2))) = k6_subset_1(X1,X2)
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_256,c_254])).

cnf(c_1956,plain,
    ( k1_relat_1(k7_relat_1(X0,k6_subset_1(k1_relat_1(X0),X1))) = k6_subset_1(k1_relat_1(X0),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_257,c_742])).

cnf(c_2114,plain,
    ( k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0))) = k6_subset_1(k1_relat_1(sK1),X0) ),
    inference(superposition,[status(thm)],[c_252,c_1956])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_253,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_392,plain,
    ( k7_relat_1(sK1,k1_relat_1(sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_252,c_253])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k6_subset_1(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_255,plain,
    ( k6_subset_1(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k6_subset_1(X1,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_619,plain,
    ( k6_subset_1(k7_relat_1(sK1,X0),k7_relat_1(sK1,X1)) = k7_relat_1(sK1,k6_subset_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_252,c_255])).

cnf(c_760,plain,
    ( k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0)) = k6_subset_1(sK1,k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_392,c_619])).

cnf(c_2115,plain,
    ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0))) = k6_subset_1(k1_relat_1(sK1),X0) ),
    inference(light_normalisation,[status(thm)],[c_2114,c_760])).

cnf(c_7,negated_conjecture,
    ( k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_2755,plain,
    ( k6_subset_1(k1_relat_1(sK1),sK0) != k6_subset_1(k1_relat_1(sK1),sK0) ),
    inference(demodulation,[status(thm)],[c_2115,c_7])).

cnf(c_117,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_671,plain,
    ( k6_subset_1(k1_relat_1(sK1),sK0) = k6_subset_1(k1_relat_1(sK1),sK0) ),
    inference(instantiation,[status(thm)],[c_117])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2755,c_671])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:43:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.13/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.00  
% 3.13/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.13/1.00  
% 3.13/1.00  ------  iProver source info
% 3.13/1.00  
% 3.13/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.13/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.13/1.00  git: non_committed_changes: false
% 3.13/1.00  git: last_make_outside_of_git: false
% 3.13/1.00  
% 3.13/1.00  ------ 
% 3.13/1.00  ------ Parsing...
% 3.13/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.13/1.00  
% 3.13/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.13/1.00  
% 3.13/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.13/1.00  
% 3.13/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.13/1.00  ------ Proving...
% 3.13/1.00  ------ Problem Properties 
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  clauses                                 8
% 3.13/1.00  conjectures                             2
% 3.13/1.00  EPR                                     3
% 3.13/1.00  Horn                                    8
% 3.13/1.00  unary                                   3
% 3.13/1.00  binary                                  3
% 3.13/1.00  lits                                    15
% 3.13/1.00  lits eq                                 5
% 3.13/1.00  fd_pure                                 0
% 3.13/1.00  fd_pseudo                               0
% 3.13/1.00  fd_cond                                 0
% 3.13/1.00  fd_pseudo_cond                          1
% 3.13/1.00  AC symbols                              0
% 3.13/1.00  
% 3.13/1.00  ------ Input Options Time Limit: Unbounded
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  ------ 
% 3.13/1.00  Current options:
% 3.13/1.00  ------ 
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  ------ Proving...
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  % SZS status Theorem for theBenchmark.p
% 3.13/1.00  
% 3.13/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.13/1.00  
% 3.13/1.00  fof(f7,conjecture,(
% 3.13/1.00    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f8,negated_conjecture,(
% 3.13/1.00    ~! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 3.13/1.00    inference(negated_conjecture,[],[f7])).
% 3.13/1.00  
% 3.13/1.00  fof(f14,plain,(
% 3.13/1.00    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 3.13/1.00    inference(ennf_transformation,[],[f8])).
% 3.13/1.00  
% 3.13/1.00  fof(f17,plain,(
% 3.13/1.00    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) & v1_relat_1(X1)) => (k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) & v1_relat_1(sK1))),
% 3.13/1.00    introduced(choice_axiom,[])).
% 3.13/1.00  
% 3.13/1.00  fof(f18,plain,(
% 3.13/1.00    k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) & v1_relat_1(sK1)),
% 3.13/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f17])).
% 3.13/1.00  
% 3.13/1.00  fof(f27,plain,(
% 3.13/1.00    v1_relat_1(sK1)),
% 3.13/1.00    inference(cnf_transformation,[],[f18])).
% 3.13/1.00  
% 3.13/1.00  fof(f1,axiom,(
% 3.13/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f15,plain,(
% 3.13/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.13/1.00    inference(nnf_transformation,[],[f1])).
% 3.13/1.00  
% 3.13/1.00  fof(f16,plain,(
% 3.13/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.13/1.00    inference(flattening,[],[f15])).
% 3.13/1.00  
% 3.13/1.00  fof(f20,plain,(
% 3.13/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.13/1.00    inference(cnf_transformation,[],[f16])).
% 3.13/1.00  
% 3.13/1.00  fof(f30,plain,(
% 3.13/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.13/1.00    inference(equality_resolution,[],[f20])).
% 3.13/1.00  
% 3.13/1.00  fof(f2,axiom,(
% 3.13/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f9,plain,(
% 3.13/1.00    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 3.13/1.00    inference(ennf_transformation,[],[f2])).
% 3.13/1.00  
% 3.13/1.00  fof(f22,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f9])).
% 3.13/1.00  
% 3.13/1.00  fof(f3,axiom,(
% 3.13/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f23,plain,(
% 3.13/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f3])).
% 3.13/1.00  
% 3.13/1.00  fof(f29,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 3.13/1.00    inference(definition_unfolding,[],[f22,f23])).
% 3.13/1.00  
% 3.13/1.00  fof(f5,axiom,(
% 3.13/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f11,plain,(
% 3.13/1.00    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.13/1.00    inference(ennf_transformation,[],[f5])).
% 3.13/1.00  
% 3.13/1.00  fof(f12,plain,(
% 3.13/1.00    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.13/1.00    inference(flattening,[],[f11])).
% 3.13/1.00  
% 3.13/1.00  fof(f25,plain,(
% 3.13/1.00    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f12])).
% 3.13/1.00  
% 3.13/1.00  fof(f6,axiom,(
% 3.13/1.00    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f13,plain,(
% 3.13/1.00    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 3.13/1.00    inference(ennf_transformation,[],[f6])).
% 3.13/1.00  
% 3.13/1.00  fof(f26,plain,(
% 3.13/1.00    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f13])).
% 3.13/1.00  
% 3.13/1.00  fof(f4,axiom,(
% 3.13/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f10,plain,(
% 3.13/1.00    ! [X0,X1,X2] : (k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_relat_1(X2))),
% 3.13/1.00    inference(ennf_transformation,[],[f4])).
% 3.13/1.00  
% 3.13/1.00  fof(f24,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_relat_1(X2)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f10])).
% 3.13/1.00  
% 3.13/1.00  fof(f28,plain,(
% 3.13/1.00    k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))),
% 3.13/1.00    inference(cnf_transformation,[],[f18])).
% 3.13/1.00  
% 3.13/1.00  cnf(c_8,negated_conjecture,
% 3.13/1.00      ( v1_relat_1(sK1) ),
% 3.13/1.00      inference(cnf_transformation,[],[f27]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_252,plain,
% 3.13/1.00      ( v1_relat_1(sK1) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1,plain,
% 3.13/1.00      ( r1_tarski(X0,X0) ),
% 3.13/1.00      inference(cnf_transformation,[],[f30]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_257,plain,
% 3.13/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3,plain,
% 3.13/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(k6_subset_1(X0,X2),X1) ),
% 3.13/1.00      inference(cnf_transformation,[],[f29]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_256,plain,
% 3.13/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.13/1.00      | r1_tarski(k6_subset_1(X0,X2),X1) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_5,plain,
% 3.13/1.00      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.13/1.00      | ~ v1_relat_1(X1)
% 3.13/1.00      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.13/1.00      inference(cnf_transformation,[],[f25]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_254,plain,
% 3.13/1.00      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 3.13/1.00      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.13/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_742,plain,
% 3.13/1.00      ( k1_relat_1(k7_relat_1(X0,k6_subset_1(X1,X2))) = k6_subset_1(X1,X2)
% 3.13/1.00      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.13/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_256,c_254]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1956,plain,
% 3.13/1.00      ( k1_relat_1(k7_relat_1(X0,k6_subset_1(k1_relat_1(X0),X1))) = k6_subset_1(k1_relat_1(X0),X1)
% 3.13/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_257,c_742]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2114,plain,
% 3.13/1.00      ( k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0))) = k6_subset_1(k1_relat_1(sK1),X0) ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_252,c_1956]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_6,plain,
% 3.13/1.00      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
% 3.13/1.00      inference(cnf_transformation,[],[f26]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_253,plain,
% 3.13/1.00      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 3.13/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_392,plain,
% 3.13/1.00      ( k7_relat_1(sK1,k1_relat_1(sK1)) = sK1 ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_252,c_253]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_4,plain,
% 3.13/1.00      ( ~ v1_relat_1(X0)
% 3.13/1.00      | k6_subset_1(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k6_subset_1(X1,X2)) ),
% 3.13/1.00      inference(cnf_transformation,[],[f24]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_255,plain,
% 3.13/1.00      ( k6_subset_1(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k6_subset_1(X1,X2))
% 3.13/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_619,plain,
% 3.13/1.00      ( k6_subset_1(k7_relat_1(sK1,X0),k7_relat_1(sK1,X1)) = k7_relat_1(sK1,k6_subset_1(X0,X1)) ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_252,c_255]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_760,plain,
% 3.13/1.00      ( k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0)) = k6_subset_1(sK1,k7_relat_1(sK1,X0)) ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_392,c_619]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2115,plain,
% 3.13/1.00      ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0))) = k6_subset_1(k1_relat_1(sK1),X0) ),
% 3.13/1.00      inference(light_normalisation,[status(thm)],[c_2114,c_760]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_7,negated_conjecture,
% 3.13/1.00      ( k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) ),
% 3.13/1.00      inference(cnf_transformation,[],[f28]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2755,plain,
% 3.13/1.00      ( k6_subset_1(k1_relat_1(sK1),sK0) != k6_subset_1(k1_relat_1(sK1),sK0) ),
% 3.13/1.00      inference(demodulation,[status(thm)],[c_2115,c_7]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_117,plain,( X0 = X0 ),theory(equality) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_671,plain,
% 3.13/1.00      ( k6_subset_1(k1_relat_1(sK1),sK0) = k6_subset_1(k1_relat_1(sK1),sK0) ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_117]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(contradiction,plain,
% 3.13/1.00      ( $false ),
% 3.13/1.00      inference(minisat,[status(thm)],[c_2755,c_671]) ).
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.13/1.00  
% 3.13/1.00  ------                               Statistics
% 3.13/1.00  
% 3.13/1.00  ------ Selected
% 3.13/1.00  
% 3.13/1.00  total_time:                             0.131
% 3.13/1.00  
%------------------------------------------------------------------------------
