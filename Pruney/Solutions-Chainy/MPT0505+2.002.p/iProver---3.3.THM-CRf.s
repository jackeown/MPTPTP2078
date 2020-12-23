%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:45:02 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 107 expanded)
%              Number of clauses        :   26 (  26 expanded)
%              Number of leaves         :   12 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :  157 ( 255 expanded)
%              Number of equality atoms :   76 ( 120 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k7_relat_1(sK3,sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1)
      & r1_tarski(sK1,sK2)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( k7_relat_1(sK3,sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1)
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f19])).

fof(f33,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X3,X2)
              & r1_tarski(X3,X1) )
           => r1_tarski(X3,X0) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
     => ( ~ r1_tarski(sK0(X0,X1,X2),X0)
        & r1_tarski(sK0(X0,X1,X2),X2)
        & r1_tarski(sK0(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ( ~ r1_tarski(sK0(X0,X1,X2),X0)
        & r1_tarski(sK0(X0,X1,X2),X2)
        & r1_tarski(sK0(X0,X1,X2),X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f17])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = X0
      | r1_tarski(sK0(X0,X1,X2),X1)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f30,f35])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = X0
      | r1_tarski(sK0(X0,X1,X2),X1)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f36])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = X0
      | ~ r1_tarski(sK0(X0,X1,X2),X0)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = X0
      | ~ r1_tarski(sK0(X0,X1,X2),X0)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f36])).

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

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f27,f35,f35])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f31,f36])).

fof(f32,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f34,plain,(
    k7_relat_1(sK3,sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_262,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(sK0(X0,X1,X2),X1)
    | k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_263,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(sK0(X2,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | ~ r1_tarski(sK0(X0,X1,X2),X0)
    | k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_265,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(sK0(X2,X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_629,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_263,c_265])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_24,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1036,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_629,c_24])).

cnf(c_1037,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1036])).

cnf(c_1041,plain,
    ( k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)) = sK1 ),
    inference(superposition,[status(thm)],[c_262,c_1037])).

cnf(c_6,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_10,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_98,plain,
    ( k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_10])).

cnf(c_99,plain,
    ( k7_relat_1(sK3,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k7_relat_1(sK3,X0),X1) ),
    inference(unflattening,[status(thm)],[c_98])).

cnf(c_330,plain,
    ( k7_relat_1(sK3,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k7_relat_1(sK3,X1),X0) ),
    inference(superposition,[status(thm)],[c_6,c_99])).

cnf(c_1222,plain,
    ( k7_relat_1(k7_relat_1(sK3,sK2),sK1) = k7_relat_1(sK3,sK1) ),
    inference(superposition,[status(thm)],[c_1041,c_330])).

cnf(c_148,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_319,plain,
    ( k7_relat_1(sK3,sK1) = k7_relat_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_148])).

cnf(c_149,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_292,plain,
    ( k7_relat_1(k7_relat_1(sK3,sK2),sK1) != X0
    | k7_relat_1(sK3,sK1) != X0
    | k7_relat_1(sK3,sK1) = k7_relat_1(k7_relat_1(sK3,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_149])).

cnf(c_318,plain,
    ( k7_relat_1(k7_relat_1(sK3,sK2),sK1) != k7_relat_1(sK3,sK1)
    | k7_relat_1(sK3,sK1) = k7_relat_1(k7_relat_1(sK3,sK2),sK1)
    | k7_relat_1(sK3,sK1) != k7_relat_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_292])).

cnf(c_8,negated_conjecture,
    ( k7_relat_1(sK3,sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1222,c_319,c_318,c_8])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:49:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.41/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/0.99  
% 3.41/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.41/0.99  
% 3.41/0.99  ------  iProver source info
% 3.41/0.99  
% 3.41/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.41/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.41/0.99  git: non_committed_changes: false
% 3.41/0.99  git: last_make_outside_of_git: false
% 3.41/0.99  
% 3.41/0.99  ------ 
% 3.41/0.99  ------ Parsing...
% 3.41/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.41/0.99  
% 3.41/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.41/0.99  
% 3.41/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.41/0.99  
% 3.41/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.41/0.99  ------ Proving...
% 3.41/0.99  ------ Problem Properties 
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  clauses                                 9
% 3.41/0.99  conjectures                             2
% 3.41/0.99  EPR                                     3
% 3.41/0.99  Horn                                    7
% 3.41/0.99  unary                                   5
% 3.41/0.99  binary                                  0
% 3.41/0.99  lits                                    20
% 3.41/0.99  lits eq                                 7
% 3.41/0.99  fd_pure                                 0
% 3.41/0.99  fd_pseudo                               0
% 3.41/0.99  fd_cond                                 0
% 3.41/0.99  fd_pseudo_cond                          4
% 3.41/0.99  AC symbols                              0
% 3.41/0.99  
% 3.41/0.99  ------ Input Options Time Limit: Unbounded
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  ------ 
% 3.41/0.99  Current options:
% 3.41/0.99  ------ 
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  ------ Proving...
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  % SZS status Theorem for theBenchmark.p
% 3.41/0.99  
% 3.41/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.41/0.99  
% 3.41/0.99  fof(f8,conjecture,(
% 3.41/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f9,negated_conjecture,(
% 3.41/0.99    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)))),
% 3.41/0.99    inference(negated_conjecture,[],[f8])).
% 3.41/0.99  
% 3.41/0.99  fof(f13,plain,(
% 3.41/0.99    ? [X0,X1,X2] : ((k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 3.41/0.99    inference(ennf_transformation,[],[f9])).
% 3.41/0.99  
% 3.41/0.99  fof(f14,plain,(
% 3.41/0.99    ? [X0,X1,X2] : (k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 3.41/0.99    inference(flattening,[],[f13])).
% 3.41/0.99  
% 3.41/0.99  fof(f19,plain,(
% 3.41/0.99    ? [X0,X1,X2] : (k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k7_relat_1(sK3,sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1) & r1_tarski(sK1,sK2) & v1_relat_1(sK3))),
% 3.41/0.99    introduced(choice_axiom,[])).
% 3.41/0.99  
% 3.41/0.99  fof(f20,plain,(
% 3.41/0.99    k7_relat_1(sK3,sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1) & r1_tarski(sK1,sK2) & v1_relat_1(sK3)),
% 3.41/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f19])).
% 3.41/0.99  
% 3.41/0.99  fof(f33,plain,(
% 3.41/0.99    r1_tarski(sK1,sK2)),
% 3.41/0.99    inference(cnf_transformation,[],[f20])).
% 3.41/0.99  
% 3.41/0.99  fof(f2,axiom,(
% 3.41/0.99    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X3,X2) & r1_tarski(X3,X1)) => r1_tarski(X3,X0)) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k3_xboole_0(X1,X2) = X0)),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f10,plain,(
% 3.41/0.99    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (? [X3] : (~r1_tarski(X3,X0) & (r1_tarski(X3,X2) & r1_tarski(X3,X1))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.41/0.99    inference(ennf_transformation,[],[f2])).
% 3.41/0.99  
% 3.41/0.99  fof(f11,plain,(
% 3.41/0.99    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | ? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.41/0.99    inference(flattening,[],[f10])).
% 3.41/0.99  
% 3.41/0.99  fof(f17,plain,(
% 3.41/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) => (~r1_tarski(sK0(X0,X1,X2),X0) & r1_tarski(sK0(X0,X1,X2),X2) & r1_tarski(sK0(X0,X1,X2),X1)))),
% 3.41/0.99    introduced(choice_axiom,[])).
% 3.41/0.99  
% 3.41/0.99  fof(f18,plain,(
% 3.41/0.99    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (~r1_tarski(sK0(X0,X1,X2),X0) & r1_tarski(sK0(X0,X1,X2),X2) & r1_tarski(sK0(X0,X1,X2),X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.41/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f17])).
% 3.41/0.99  
% 3.41/0.99  fof(f24,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = X0 | r1_tarski(sK0(X0,X1,X2),X1) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f18])).
% 3.41/0.99  
% 3.41/0.99  fof(f6,axiom,(
% 3.41/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f30,plain,(
% 3.41/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.41/0.99    inference(cnf_transformation,[],[f6])).
% 3.41/0.99  
% 3.41/0.99  fof(f4,axiom,(
% 3.41/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f28,plain,(
% 3.41/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f4])).
% 3.41/0.99  
% 3.41/0.99  fof(f5,axiom,(
% 3.41/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f29,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f5])).
% 3.41/0.99  
% 3.41/0.99  fof(f35,plain,(
% 3.41/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.41/0.99    inference(definition_unfolding,[],[f28,f29])).
% 3.41/0.99  
% 3.41/0.99  fof(f36,plain,(
% 3.41/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 3.41/0.99    inference(definition_unfolding,[],[f30,f35])).
% 3.41/0.99  
% 3.41/0.99  fof(f39,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = X0 | r1_tarski(sK0(X0,X1,X2),X1) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.41/0.99    inference(definition_unfolding,[],[f24,f36])).
% 3.41/0.99  
% 3.41/0.99  fof(f26,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = X0 | ~r1_tarski(sK0(X0,X1,X2),X0) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f18])).
% 3.41/0.99  
% 3.41/0.99  fof(f37,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = X0 | ~r1_tarski(sK0(X0,X1,X2),X0) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.41/0.99    inference(definition_unfolding,[],[f26,f36])).
% 3.41/0.99  
% 3.41/0.99  fof(f1,axiom,(
% 3.41/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f15,plain,(
% 3.41/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.41/0.99    inference(nnf_transformation,[],[f1])).
% 3.41/0.99  
% 3.41/0.99  fof(f16,plain,(
% 3.41/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.41/0.99    inference(flattening,[],[f15])).
% 3.41/0.99  
% 3.41/0.99  fof(f21,plain,(
% 3.41/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.41/0.99    inference(cnf_transformation,[],[f16])).
% 3.41/0.99  
% 3.41/0.99  fof(f43,plain,(
% 3.41/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.41/0.99    inference(equality_resolution,[],[f21])).
% 3.41/0.99  
% 3.41/0.99  fof(f3,axiom,(
% 3.41/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f27,plain,(
% 3.41/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f3])).
% 3.41/0.99  
% 3.41/0.99  fof(f40,plain,(
% 3.41/0.99    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 3.41/0.99    inference(definition_unfolding,[],[f27,f35,f35])).
% 3.41/0.99  
% 3.41/0.99  fof(f7,axiom,(
% 3.41/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f12,plain,(
% 3.41/0.99    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 3.41/0.99    inference(ennf_transformation,[],[f7])).
% 3.41/0.99  
% 3.41/0.99  fof(f31,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f12])).
% 3.41/0.99  
% 3.41/0.99  fof(f41,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 3.41/0.99    inference(definition_unfolding,[],[f31,f36])).
% 3.41/0.99  
% 3.41/0.99  fof(f32,plain,(
% 3.41/0.99    v1_relat_1(sK3)),
% 3.41/0.99    inference(cnf_transformation,[],[f20])).
% 3.41/0.99  
% 3.41/0.99  fof(f34,plain,(
% 3.41/0.99    k7_relat_1(sK3,sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1)),
% 3.41/0.99    inference(cnf_transformation,[],[f20])).
% 3.41/0.99  
% 3.41/0.99  cnf(c_9,negated_conjecture,
% 3.41/0.99      ( r1_tarski(sK1,sK2) ),
% 3.41/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_262,plain,
% 3.41/0.99      ( r1_tarski(sK1,sK2) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5,plain,
% 3.41/0.99      ( ~ r1_tarski(X0,X1)
% 3.41/0.99      | ~ r1_tarski(X0,X2)
% 3.41/0.99      | r1_tarski(sK0(X0,X1,X2),X1)
% 3.41/0.99      | k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = X0 ),
% 3.41/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_263,plain,
% 3.41/0.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2
% 3.41/0.99      | r1_tarski(X2,X0) != iProver_top
% 3.41/0.99      | r1_tarski(X2,X1) != iProver_top
% 3.41/0.99      | r1_tarski(sK0(X2,X0,X1),X0) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_3,plain,
% 3.41/0.99      ( ~ r1_tarski(X0,X1)
% 3.41/0.99      | ~ r1_tarski(X0,X2)
% 3.41/0.99      | ~ r1_tarski(sK0(X0,X1,X2),X0)
% 3.41/0.99      | k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = X0 ),
% 3.41/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_265,plain,
% 3.41/0.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2
% 3.41/0.99      | r1_tarski(X2,X0) != iProver_top
% 3.41/0.99      | r1_tarski(X2,X1) != iProver_top
% 3.41/0.99      | r1_tarski(sK0(X2,X0,X1),X2) != iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_629,plain,
% 3.41/0.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0
% 3.41/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.41/0.99      | r1_tarski(X0,X0) != iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_263,c_265]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_2,plain,
% 3.41/0.99      ( r1_tarski(X0,X0) ),
% 3.41/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_24,plain,
% 3.41/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1036,plain,
% 3.41/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.41/0.99      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0 ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_629,c_24]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1037,plain,
% 3.41/0.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0
% 3.41/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.41/0.99      inference(renaming,[status(thm)],[c_1036]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1041,plain,
% 3.41/0.99      ( k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)) = sK1 ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_262,c_1037]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_6,plain,
% 3.41/0.99      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 3.41/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_7,plain,
% 3.41/0.99      ( ~ v1_relat_1(X0)
% 3.41/0.99      | k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
% 3.41/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_10,negated_conjecture,
% 3.41/0.99      ( v1_relat_1(sK3) ),
% 3.41/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_98,plain,
% 3.41/0.99      ( k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
% 3.41/0.99      | sK3 != X0 ),
% 3.41/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_10]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_99,plain,
% 3.41/0.99      ( k7_relat_1(sK3,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k7_relat_1(sK3,X0),X1) ),
% 3.41/0.99      inference(unflattening,[status(thm)],[c_98]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_330,plain,
% 3.41/0.99      ( k7_relat_1(sK3,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k7_relat_1(sK3,X1),X0) ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_6,c_99]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1222,plain,
% 3.41/0.99      ( k7_relat_1(k7_relat_1(sK3,sK2),sK1) = k7_relat_1(sK3,sK1) ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_1041,c_330]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_148,plain,( X0 = X0 ),theory(equality) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_319,plain,
% 3.41/0.99      ( k7_relat_1(sK3,sK1) = k7_relat_1(sK3,sK1) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_148]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_149,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_292,plain,
% 3.41/0.99      ( k7_relat_1(k7_relat_1(sK3,sK2),sK1) != X0
% 3.41/0.99      | k7_relat_1(sK3,sK1) != X0
% 3.41/0.99      | k7_relat_1(sK3,sK1) = k7_relat_1(k7_relat_1(sK3,sK2),sK1) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_149]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_318,plain,
% 3.41/0.99      ( k7_relat_1(k7_relat_1(sK3,sK2),sK1) != k7_relat_1(sK3,sK1)
% 3.41/0.99      | k7_relat_1(sK3,sK1) = k7_relat_1(k7_relat_1(sK3,sK2),sK1)
% 3.41/0.99      | k7_relat_1(sK3,sK1) != k7_relat_1(sK3,sK1) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_292]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_8,negated_conjecture,
% 3.41/0.99      ( k7_relat_1(sK3,sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1) ),
% 3.41/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(contradiction,plain,
% 3.41/0.99      ( $false ),
% 3.41/0.99      inference(minisat,[status(thm)],[c_1222,c_319,c_318,c_8]) ).
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.41/0.99  
% 3.41/0.99  ------                               Statistics
% 3.41/0.99  
% 3.41/0.99  ------ Selected
% 3.41/0.99  
% 3.41/0.99  total_time:                             0.081
% 3.41/0.99  
%------------------------------------------------------------------------------
