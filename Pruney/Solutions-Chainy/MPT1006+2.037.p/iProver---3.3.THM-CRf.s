%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:37 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 149 expanded)
%              Number of clauses        :   33 (  55 expanded)
%              Number of leaves         :    8 (  26 expanded)
%              Depth                    :   18
%              Number of atoms          :  123 ( 371 expanded)
%              Number of equality atoms :   67 ( 155 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f12,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_1(X2) )
   => ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
     => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f15])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f33,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_422,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1217,plain,
    ( k1_xboole_0 != X0
    | r1_xboole_0(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_422])).

cnf(c_1322,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1217])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_417,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1327,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1322,c_417])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_415,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k8_relset_1(X1,X2,X0,X3),X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_416,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k8_relset_1(X1,X2,X0,X3),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_420,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1109,plain,
    ( k3_xboole_0(k8_relset_1(X0,X1,X2,X3),X0) = k8_relset_1(X0,X1,X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_416,c_420])).

cnf(c_1701,plain,
    ( k3_xboole_0(k8_relset_1(k1_xboole_0,sK0,sK2,X0),k1_xboole_0) = k8_relset_1(k1_xboole_0,sK0,sK2,X0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_415,c_1109])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_13,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2217,plain,
    ( k3_xboole_0(k8_relset_1(k1_xboole_0,sK0,sK2,X0),k1_xboole_0) = k8_relset_1(k1_xboole_0,sK0,sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1701,c_13])).

cnf(c_5,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_2223,plain,
    ( k3_xboole_0(k8_relset_1(k1_xboole_0,sK0,sK2,X0),k4_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(k8_relset_1(k1_xboole_0,sK0,sK2,X0),X1) ),
    inference(superposition,[status(thm)],[c_2217,c_5])).

cnf(c_2237,plain,
    ( k4_xboole_0(k8_relset_1(k1_xboole_0,sK0,sK2,X0),k1_xboole_0) = k3_xboole_0(k8_relset_1(k1_xboole_0,sK0,sK2,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1327,c_2223])).

cnf(c_2258,plain,
    ( k4_xboole_0(k8_relset_1(k1_xboole_0,sK0,sK2,X0),k1_xboole_0) = k8_relset_1(k1_xboole_0,sK0,sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_2237,c_2217])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_418,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2379,plain,
    ( r1_xboole_0(k8_relset_1(k1_xboole_0,sK0,sK2,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2258,c_418])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_421,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2592,plain,
    ( k3_xboole_0(k8_relset_1(k1_xboole_0,sK0,sK2,X0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2379,c_421])).

cnf(c_4158,plain,
    ( k8_relset_1(k1_xboole_0,sK0,sK2,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2592,c_2217])).

cnf(c_10,negated_conjecture,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_4170,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4158,c_10])).

cnf(c_4187,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_4170])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:01:38 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 3.49/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/0.98  
% 3.49/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.49/0.98  
% 3.49/0.98  ------  iProver source info
% 3.49/0.98  
% 3.49/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.49/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.49/0.98  git: non_committed_changes: false
% 3.49/0.98  git: last_make_outside_of_git: false
% 3.49/0.98  
% 3.49/0.98  ------ 
% 3.49/0.98  ------ Parsing...
% 3.49/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.49/0.98  
% 3.49/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.49/0.98  
% 3.49/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.49/0.98  
% 3.49/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.49/0.98  ------ Proving...
% 3.49/0.98  ------ Problem Properties 
% 3.49/0.98  
% 3.49/0.98  
% 3.49/0.98  clauses                                 13
% 3.49/0.98  conjectures                             3
% 3.49/0.98  EPR                                     1
% 3.49/0.98  Horn                                    13
% 3.49/0.98  unary                                   6
% 3.49/0.98  binary                                  6
% 3.49/0.98  lits                                    21
% 3.49/0.98  lits eq                                 10
% 3.49/0.98  fd_pure                                 0
% 3.49/0.98  fd_pseudo                               0
% 3.49/0.98  fd_cond                                 0
% 3.49/0.98  fd_pseudo_cond                          0
% 3.49/0.98  AC symbols                              0
% 3.49/0.98  
% 3.49/0.98  ------ Input Options Time Limit: Unbounded
% 3.49/0.98  
% 3.49/0.98  
% 3.49/0.98  ------ 
% 3.49/0.98  Current options:
% 3.49/0.98  ------ 
% 3.49/0.98  
% 3.49/0.98  
% 3.49/0.98  
% 3.49/0.98  
% 3.49/0.98  ------ Proving...
% 3.49/0.98  
% 3.49/0.98  
% 3.49/0.98  % SZS status Theorem for theBenchmark.p
% 3.49/0.98  
% 3.49/0.98   Resolution empty clause
% 3.49/0.98  
% 3.49/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.49/0.98  
% 3.49/0.98  fof(f2,axiom,(
% 3.49/0.98    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.49/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/0.98  
% 3.49/0.98  fof(f11,plain,(
% 3.49/0.98    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.49/0.98    inference(rectify,[],[f2])).
% 3.49/0.98  
% 3.49/0.98  fof(f25,plain,(
% 3.49/0.98    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.49/0.98    inference(cnf_transformation,[],[f11])).
% 3.49/0.98  
% 3.49/0.98  fof(f1,axiom,(
% 3.49/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.49/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/0.98  
% 3.49/0.98  fof(f19,plain,(
% 3.49/0.98    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.49/0.98    inference(nnf_transformation,[],[f1])).
% 3.49/0.98  
% 3.49/0.98  fof(f24,plain,(
% 3.49/0.98    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.49/0.98    inference(cnf_transformation,[],[f19])).
% 3.49/0.98  
% 3.49/0.98  fof(f7,axiom,(
% 3.49/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.49/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/0.98  
% 3.49/0.98  fof(f20,plain,(
% 3.49/0.98    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.49/0.98    inference(nnf_transformation,[],[f7])).
% 3.49/0.98  
% 3.49/0.98  fof(f30,plain,(
% 3.49/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.49/0.98    inference(cnf_transformation,[],[f20])).
% 3.49/0.98  
% 3.49/0.98  fof(f9,conjecture,(
% 3.49/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 3.49/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/0.98  
% 3.49/0.98  fof(f10,negated_conjecture,(
% 3.49/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 3.49/0.98    inference(negated_conjecture,[],[f9])).
% 3.49/0.98  
% 3.49/0.98  fof(f12,plain,(
% 3.49/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 3.49/0.98    inference(pure_predicate_removal,[],[f10])).
% 3.49/0.98  
% 3.49/0.98  fof(f17,plain,(
% 3.49/0.98    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)))),
% 3.49/0.98    inference(ennf_transformation,[],[f12])).
% 3.49/0.98  
% 3.49/0.98  fof(f18,plain,(
% 3.49/0.98    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2))),
% 3.49/0.98    inference(flattening,[],[f17])).
% 3.49/0.98  
% 3.49/0.98  fof(f21,plain,(
% 3.49/0.98    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)) => (k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_1(sK2))),
% 3.49/0.98    introduced(choice_axiom,[])).
% 3.49/0.98  
% 3.49/0.98  fof(f22,plain,(
% 3.49/0.98    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_1(sK2)),
% 3.49/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21])).
% 3.49/0.98  
% 3.49/0.98  fof(f34,plain,(
% 3.49/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 3.49/0.98    inference(cnf_transformation,[],[f22])).
% 3.49/0.98  
% 3.49/0.98  fof(f8,axiom,(
% 3.49/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0))),
% 3.49/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/0.98  
% 3.49/0.98  fof(f15,plain,(
% 3.49/0.98    ! [X0,X1,X2,X3] : (r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)))),
% 3.49/0.98    inference(ennf_transformation,[],[f8])).
% 3.49/0.98  
% 3.49/0.98  fof(f16,plain,(
% 3.49/0.98    ! [X0,X1,X2,X3] : (r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))),
% 3.49/0.98    inference(flattening,[],[f15])).
% 3.49/0.98  
% 3.49/0.98  fof(f32,plain,(
% 3.49/0.98    ( ! [X2,X0,X3,X1] : (r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) )),
% 3.49/0.98    inference(cnf_transformation,[],[f16])).
% 3.49/0.98  
% 3.49/0.98  fof(f4,axiom,(
% 3.49/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.49/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/0.98  
% 3.49/0.98  fof(f13,plain,(
% 3.49/0.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.49/0.98    inference(ennf_transformation,[],[f4])).
% 3.49/0.98  
% 3.49/0.98  fof(f27,plain,(
% 3.49/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.49/0.98    inference(cnf_transformation,[],[f13])).
% 3.49/0.98  
% 3.49/0.98  fof(f33,plain,(
% 3.49/0.98    v1_funct_1(sK2)),
% 3.49/0.98    inference(cnf_transformation,[],[f22])).
% 3.49/0.98  
% 3.49/0.98  fof(f5,axiom,(
% 3.49/0.98    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.49/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/0.98  
% 3.49/0.98  fof(f28,plain,(
% 3.49/0.98    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.49/0.98    inference(cnf_transformation,[],[f5])).
% 3.49/0.98  
% 3.49/0.98  fof(f31,plain,(
% 3.49/0.98    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.49/0.98    inference(cnf_transformation,[],[f20])).
% 3.49/0.98  
% 3.49/0.98  fof(f23,plain,(
% 3.49/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.49/0.98    inference(cnf_transformation,[],[f19])).
% 3.49/0.98  
% 3.49/0.98  fof(f35,plain,(
% 3.49/0.98    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 3.49/0.98    inference(cnf_transformation,[],[f22])).
% 3.49/0.98  
% 3.49/0.98  cnf(c_2,plain,
% 3.49/0.98      ( k3_xboole_0(X0,X0) = X0 ),
% 3.49/0.98      inference(cnf_transformation,[],[f25]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_0,plain,
% 3.49/0.98      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 3.49/0.98      inference(cnf_transformation,[],[f24]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_422,plain,
% 3.49/0.98      ( k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1) = iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1217,plain,
% 3.49/0.98      ( k1_xboole_0 != X0 | r1_xboole_0(X0,X0) = iProver_top ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_2,c_422]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1322,plain,
% 3.49/0.98      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.49/0.98      inference(equality_resolution,[status(thm)],[c_1217]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_8,plain,
% 3.49/0.98      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.49/0.98      inference(cnf_transformation,[],[f30]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_417,plain,
% 3.49/0.98      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1327,plain,
% 3.49/0.98      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_1322,c_417]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_11,negated_conjecture,
% 3.49/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
% 3.49/0.98      inference(cnf_transformation,[],[f34]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_415,plain,
% 3.49/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) = iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_9,plain,
% 3.49/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.49/0.98      | r1_tarski(k8_relset_1(X1,X2,X0,X3),X1)
% 3.49/0.98      | ~ v1_funct_1(X0) ),
% 3.49/0.98      inference(cnf_transformation,[],[f32]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_416,plain,
% 3.49/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.49/0.98      | r1_tarski(k8_relset_1(X1,X2,X0,X3),X1) = iProver_top
% 3.49/0.98      | v1_funct_1(X0) != iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_4,plain,
% 3.49/0.98      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.49/0.98      inference(cnf_transformation,[],[f27]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_420,plain,
% 3.49/0.98      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1109,plain,
% 3.49/0.98      ( k3_xboole_0(k8_relset_1(X0,X1,X2,X3),X0) = k8_relset_1(X0,X1,X2,X3)
% 3.49/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.49/0.98      | v1_funct_1(X2) != iProver_top ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_416,c_420]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1701,plain,
% 3.49/0.98      ( k3_xboole_0(k8_relset_1(k1_xboole_0,sK0,sK2,X0),k1_xboole_0) = k8_relset_1(k1_xboole_0,sK0,sK2,X0)
% 3.49/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_415,c_1109]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_12,negated_conjecture,
% 3.49/0.98      ( v1_funct_1(sK2) ),
% 3.49/0.98      inference(cnf_transformation,[],[f33]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_13,plain,
% 3.49/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_2217,plain,
% 3.49/0.98      ( k3_xboole_0(k8_relset_1(k1_xboole_0,sK0,sK2,X0),k1_xboole_0) = k8_relset_1(k1_xboole_0,sK0,sK2,X0) ),
% 3.49/0.98      inference(global_propositional_subsumption,[status(thm)],[c_1701,c_13]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_5,plain,
% 3.49/0.98      ( k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 3.49/0.98      inference(cnf_transformation,[],[f28]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_2223,plain,
% 3.49/0.98      ( k3_xboole_0(k8_relset_1(k1_xboole_0,sK0,sK2,X0),k4_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(k8_relset_1(k1_xboole_0,sK0,sK2,X0),X1) ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_2217,c_5]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_2237,plain,
% 3.49/0.98      ( k4_xboole_0(k8_relset_1(k1_xboole_0,sK0,sK2,X0),k1_xboole_0) = k3_xboole_0(k8_relset_1(k1_xboole_0,sK0,sK2,X0),k1_xboole_0) ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_1327,c_2223]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_2258,plain,
% 3.49/0.98      ( k4_xboole_0(k8_relset_1(k1_xboole_0,sK0,sK2,X0),k1_xboole_0) = k8_relset_1(k1_xboole_0,sK0,sK2,X0) ),
% 3.49/0.98      inference(light_normalisation,[status(thm)],[c_2237,c_2217]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_7,plain,
% 3.49/0.98      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 3.49/0.98      inference(cnf_transformation,[],[f31]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_418,plain,
% 3.49/0.98      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_2379,plain,
% 3.49/0.98      ( r1_xboole_0(k8_relset_1(k1_xboole_0,sK0,sK2,X0),k1_xboole_0) = iProver_top ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_2258,c_418]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1,plain,
% 3.49/0.98      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.49/0.98      inference(cnf_transformation,[],[f23]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_421,plain,
% 3.49/0.98      ( k3_xboole_0(X0,X1) = k1_xboole_0 | r1_xboole_0(X0,X1) != iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_2592,plain,
% 3.49/0.98      ( k3_xboole_0(k8_relset_1(k1_xboole_0,sK0,sK2,X0),k1_xboole_0) = k1_xboole_0 ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_2379,c_421]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_4158,plain,
% 3.49/0.98      ( k8_relset_1(k1_xboole_0,sK0,sK2,X0) = k1_xboole_0 ),
% 3.49/0.98      inference(demodulation,[status(thm)],[c_2592,c_2217]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_10,negated_conjecture,
% 3.49/0.98      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
% 3.49/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_4170,plain,
% 3.49/0.98      ( k1_xboole_0 != k1_xboole_0 ),
% 3.49/0.98      inference(demodulation,[status(thm)],[c_4158,c_10]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_4187,plain,
% 3.49/0.98      ( $false ),
% 3.49/0.98      inference(equality_resolution_simp,[status(thm)],[c_4170]) ).
% 3.49/0.98  
% 3.49/0.98  
% 3.49/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.49/0.98  
% 3.49/0.98  ------                               Statistics
% 3.49/0.98  
% 3.49/0.98  ------ Selected
% 3.49/0.98  
% 3.49/0.98  total_time:                             0.122
% 3.49/0.98  
%------------------------------------------------------------------------------
