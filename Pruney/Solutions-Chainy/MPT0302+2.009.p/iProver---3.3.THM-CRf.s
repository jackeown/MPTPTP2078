%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:04 EST 2020

% Result     : Theorem 7.80s
% Output     : CNFRefutation 7.80s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 244 expanded)
%              Number of clauses        :   41 (  81 expanded)
%              Number of leaves         :    9 (  47 expanded)
%              Depth                    :   18
%              Number of atoms          :  201 ( 777 expanded)
%              Number of equality atoms :  101 ( 394 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f15,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f21])).

fof(f43,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f19,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f20,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f19])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) )
   => ( sK8 != sK9
      & k1_xboole_0 != sK9
      & k1_xboole_0 != sK8
      & k2_zfmisc_1(sK8,sK9) = k2_zfmisc_1(sK9,sK8) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( sK8 != sK9
    & k1_xboole_0 != sK9
    & k1_xboole_0 != sK8
    & k2_zfmisc_1(sK8,sK9) = k2_zfmisc_1(sK9,sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f20,f41])).

fof(f69,plain,(
    k2_zfmisc_1(sK8,sK9) = k2_zfmisc_1(sK9,sK8) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f37])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f71,plain,(
    k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f70,plain,(
    k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,(
    sK8 != sK9 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_32145,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_29,negated_conjecture,
    ( k2_zfmisc_1(sK8,sK9) = k2_zfmisc_1(sK9,sK8) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_32137,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_33683,plain,
    ( r2_hidden(X0,sK9) != iProver_top
    | r2_hidden(X1,sK8) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK8,sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_29,c_32137])).

cnf(c_21,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_32136,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_33909,plain,
    ( r2_hidden(X0,sK9) != iProver_top
    | r2_hidden(X1,sK9) = iProver_top
    | r2_hidden(X1,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_33683,c_32136])).

cnf(c_34341,plain,
    ( r2_hidden(X0,sK9) = iProver_top
    | r2_hidden(X0,sK8) != iProver_top
    | v1_xboole_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_32145,c_33909])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1108,plain,
    ( ~ v1_xboole_0(sK9)
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1109,plain,
    ( k1_xboole_0 = sK9
    | v1_xboole_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1108])).

cnf(c_34362,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(X0,sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_34341,c_27,c_1109])).

cnf(c_34363,plain,
    ( r2_hidden(X0,sK9) = iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_34362])).

cnf(c_34370,plain,
    ( r2_hidden(sK0(sK8),sK9) = iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_32145,c_34363])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1822,plain,
    ( ~ v1_xboole_0(sK8)
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1823,plain,
    ( k1_xboole_0 = sK8
    | v1_xboole_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1822])).

cnf(c_34777,plain,
    ( r2_hidden(sK0(sK8),sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_34370,c_28,c_1823])).

cnf(c_32628,plain,
    ( r2_hidden(X0,sK8) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_29,c_32136])).

cnf(c_33685,plain,
    ( r2_hidden(X0,sK9) != iProver_top
    | r2_hidden(X1,sK8) != iProver_top
    | r2_hidden(X0,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_32137,c_32628])).

cnf(c_34783,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(sK0(sK8),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_34777,c_33685])).

cnf(c_1830,plain,
    ( r2_hidden(sK0(sK8),sK8)
    | v1_xboole_0(sK8) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1831,plain,
    ( r2_hidden(sK0(sK8),sK8) = iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1830])).

cnf(c_34792,plain,
    ( r2_hidden(sK0(sK8),sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_34783,c_28,c_1823,c_1831])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_32143,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_34118,plain,
    ( r1_tarski(sK9,X0) = iProver_top
    | r2_hidden(X1,sK8) != iProver_top
    | r2_hidden(sK1(sK9,X0),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_32143,c_33685])).

cnf(c_34799,plain,
    ( r1_tarski(sK9,X0) = iProver_top
    | r2_hidden(sK1(sK9,X0),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_34792,c_34118])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_32144,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_35600,plain,
    ( r1_tarski(sK9,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_34799,c_32144])).

cnf(c_34371,plain,
    ( r1_tarski(sK8,X0) = iProver_top
    | r2_hidden(sK1(sK8,X0),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_32143,c_34363])).

cnf(c_35104,plain,
    ( r1_tarski(sK8,sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_34371,c_32144])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_26,negated_conjecture,
    ( sK8 != sK9 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_5215,plain,
    ( ~ r1_tarski(sK9,sK8)
    | ~ r1_tarski(sK8,sK9) ),
    inference(resolution,[status(thm)],[c_7,c_26])).

cnf(c_5216,plain,
    ( r1_tarski(sK9,sK8) != iProver_top
    | r1_tarski(sK8,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5215])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35600,c_35104,c_5216])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:50:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.80/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.80/1.50  
% 7.80/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.80/1.50  
% 7.80/1.50  ------  iProver source info
% 7.80/1.50  
% 7.80/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.80/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.80/1.50  git: non_committed_changes: false
% 7.80/1.50  git: last_make_outside_of_git: false
% 7.80/1.50  
% 7.80/1.50  ------ 
% 7.80/1.50  ------ Parsing...
% 7.80/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.80/1.50  
% 7.80/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.80/1.50  
% 7.80/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.80/1.50  
% 7.80/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.80/1.50  ------ Proving...
% 7.80/1.50  ------ Problem Properties 
% 7.80/1.50  
% 7.80/1.50  
% 7.80/1.50  clauses                                 28
% 7.80/1.50  conjectures                             4
% 7.80/1.50  EPR                                     8
% 7.80/1.50  Horn                                    21
% 7.80/1.50  unary                                   9
% 7.80/1.50  binary                                  11
% 7.80/1.50  lits                                    57
% 7.80/1.50  lits eq                                 19
% 7.80/1.50  fd_pure                                 0
% 7.80/1.50  fd_pseudo                               0
% 7.80/1.50  fd_cond                                 2
% 7.80/1.50  fd_pseudo_cond                          5
% 7.80/1.50  AC symbols                              0
% 7.80/1.50  
% 7.80/1.50  ------ Input Options Time Limit: Unbounded
% 7.80/1.50  
% 7.80/1.50  
% 7.80/1.50  
% 7.80/1.50  
% 7.80/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.80/1.50  Current options:
% 7.80/1.50  ------ 
% 7.80/1.50  
% 7.80/1.50  
% 7.80/1.50  
% 7.80/1.50  
% 7.80/1.50  ------ Proving...
% 7.80/1.50  
% 7.80/1.50  
% 7.80/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.80/1.50  
% 7.80/1.50  ------ Proving...
% 7.80/1.50  
% 7.80/1.50  
% 7.80/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.80/1.50  
% 7.80/1.50  ------ Proving...
% 7.80/1.50  
% 7.80/1.50  
% 7.80/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.80/1.50  
% 7.80/1.50  ------ Proving...
% 7.80/1.50  
% 7.80/1.50  
% 7.80/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.80/1.50  
% 7.80/1.50  ------ Proving...
% 7.80/1.50  
% 7.80/1.50  
% 7.80/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.80/1.50  
% 7.80/1.50  ------ Proving...
% 7.80/1.50  
% 7.80/1.50  
% 7.80/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.80/1.50  
% 7.80/1.50  ------ Proving...
% 7.80/1.50  
% 7.80/1.50  
% 7.80/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.80/1.50  
% 7.80/1.50  ------ Proving...
% 7.80/1.50  
% 7.80/1.50  
% 7.80/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.80/1.50  
% 7.80/1.50  ------ Proving...
% 7.80/1.50  
% 7.80/1.50  
% 7.80/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.80/1.50  
% 7.80/1.50  ------ Proving...
% 7.80/1.50  
% 7.80/1.50  
% 7.80/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.80/1.50  
% 7.80/1.50  ------ Proving...
% 7.80/1.50  
% 7.80/1.50  
% 7.80/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.80/1.50  
% 7.80/1.50  ------ Proving...
% 7.80/1.50  
% 7.80/1.50  
% 7.80/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.80/1.50  
% 7.80/1.50  ------ Proving...
% 7.80/1.50  
% 7.80/1.50  
% 7.80/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.80/1.50  
% 7.80/1.50  ------ Proving...
% 7.80/1.50  
% 7.80/1.50  
% 7.80/1.50  % SZS status Theorem for theBenchmark.p
% 7.80/1.50  
% 7.80/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.80/1.50  
% 7.80/1.50  fof(f1,axiom,(
% 7.80/1.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.80/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.50  
% 7.80/1.50  fof(f14,plain,(
% 7.80/1.50    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 7.80/1.50    inference(unused_predicate_definition_removal,[],[f1])).
% 7.80/1.50  
% 7.80/1.50  fof(f15,plain,(
% 7.80/1.50    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 7.80/1.50    inference(ennf_transformation,[],[f14])).
% 7.80/1.50  
% 7.80/1.50  fof(f21,plain,(
% 7.80/1.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.80/1.50    introduced(choice_axiom,[])).
% 7.80/1.50  
% 7.80/1.50  fof(f22,plain,(
% 7.80/1.50    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0))),
% 7.80/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f21])).
% 7.80/1.50  
% 7.80/1.50  fof(f43,plain,(
% 7.80/1.50    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 7.80/1.50    inference(cnf_transformation,[],[f22])).
% 7.80/1.50  
% 7.80/1.50  fof(f11,conjecture,(
% 7.80/1.50    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.80/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.50  
% 7.80/1.50  fof(f12,negated_conjecture,(
% 7.80/1.50    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.80/1.50    inference(negated_conjecture,[],[f11])).
% 7.80/1.50  
% 7.80/1.50  fof(f19,plain,(
% 7.80/1.50    ? [X0,X1] : ((X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 7.80/1.50    inference(ennf_transformation,[],[f12])).
% 7.80/1.50  
% 7.80/1.50  fof(f20,plain,(
% 7.80/1.50    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 7.80/1.50    inference(flattening,[],[f19])).
% 7.80/1.50  
% 7.80/1.50  fof(f41,plain,(
% 7.80/1.50    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)) => (sK8 != sK9 & k1_xboole_0 != sK9 & k1_xboole_0 != sK8 & k2_zfmisc_1(sK8,sK9) = k2_zfmisc_1(sK9,sK8))),
% 7.80/1.50    introduced(choice_axiom,[])).
% 7.80/1.50  
% 7.80/1.50  fof(f42,plain,(
% 7.80/1.50    sK8 != sK9 & k1_xboole_0 != sK9 & k1_xboole_0 != sK8 & k2_zfmisc_1(sK8,sK9) = k2_zfmisc_1(sK9,sK8)),
% 7.80/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f20,f41])).
% 7.80/1.50  
% 7.80/1.50  fof(f69,plain,(
% 7.80/1.50    k2_zfmisc_1(sK8,sK9) = k2_zfmisc_1(sK9,sK8)),
% 7.80/1.50    inference(cnf_transformation,[],[f42])).
% 7.80/1.50  
% 7.80/1.50  fof(f9,axiom,(
% 7.80/1.50    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 7.80/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.50  
% 7.80/1.50  fof(f37,plain,(
% 7.80/1.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 7.80/1.50    inference(nnf_transformation,[],[f9])).
% 7.80/1.50  
% 7.80/1.50  fof(f38,plain,(
% 7.80/1.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 7.80/1.50    inference(flattening,[],[f37])).
% 7.80/1.50  
% 7.80/1.50  fof(f65,plain,(
% 7.80/1.50    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 7.80/1.50    inference(cnf_transformation,[],[f38])).
% 7.80/1.50  
% 7.80/1.50  fof(f64,plain,(
% 7.80/1.50    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 7.80/1.50    inference(cnf_transformation,[],[f38])).
% 7.80/1.50  
% 7.80/1.50  fof(f71,plain,(
% 7.80/1.50    k1_xboole_0 != sK9),
% 7.80/1.50    inference(cnf_transformation,[],[f42])).
% 7.80/1.50  
% 7.80/1.50  fof(f3,axiom,(
% 7.80/1.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 7.80/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.50  
% 7.80/1.50  fof(f17,plain,(
% 7.80/1.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 7.80/1.50    inference(ennf_transformation,[],[f3])).
% 7.80/1.50  
% 7.80/1.50  fof(f47,plain,(
% 7.80/1.50    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.80/1.50    inference(cnf_transformation,[],[f17])).
% 7.80/1.50  
% 7.80/1.50  fof(f70,plain,(
% 7.80/1.50    k1_xboole_0 != sK8),
% 7.80/1.50    inference(cnf_transformation,[],[f42])).
% 7.80/1.50  
% 7.80/1.50  fof(f2,axiom,(
% 7.80/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.80/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.50  
% 7.80/1.50  fof(f16,plain,(
% 7.80/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.80/1.50    inference(ennf_transformation,[],[f2])).
% 7.80/1.50  
% 7.80/1.50  fof(f23,plain,(
% 7.80/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.80/1.50    inference(nnf_transformation,[],[f16])).
% 7.80/1.50  
% 7.80/1.50  fof(f24,plain,(
% 7.80/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.80/1.50    inference(rectify,[],[f23])).
% 7.80/1.50  
% 7.80/1.50  fof(f25,plain,(
% 7.80/1.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.80/1.50    introduced(choice_axiom,[])).
% 7.80/1.50  
% 7.80/1.50  fof(f26,plain,(
% 7.80/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.80/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).
% 7.80/1.50  
% 7.80/1.50  fof(f45,plain,(
% 7.80/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 7.80/1.50    inference(cnf_transformation,[],[f26])).
% 7.80/1.50  
% 7.80/1.50  fof(f46,plain,(
% 7.80/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 7.80/1.50    inference(cnf_transformation,[],[f26])).
% 7.80/1.50  
% 7.80/1.50  fof(f5,axiom,(
% 7.80/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.80/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.80/1.50  
% 7.80/1.50  fof(f29,plain,(
% 7.80/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.80/1.50    inference(nnf_transformation,[],[f5])).
% 7.80/1.50  
% 7.80/1.50  fof(f30,plain,(
% 7.80/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.80/1.50    inference(flattening,[],[f29])).
% 7.80/1.50  
% 7.80/1.50  fof(f52,plain,(
% 7.80/1.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.80/1.50    inference(cnf_transformation,[],[f30])).
% 7.80/1.50  
% 7.80/1.50  fof(f72,plain,(
% 7.80/1.50    sK8 != sK9),
% 7.80/1.50    inference(cnf_transformation,[],[f42])).
% 7.80/1.50  
% 7.80/1.50  cnf(c_0,plain,
% 7.80/1.50      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 7.80/1.50      inference(cnf_transformation,[],[f43]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_32145,plain,
% 7.80/1.50      ( r2_hidden(sK0(X0),X0) = iProver_top
% 7.80/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.80/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_29,negated_conjecture,
% 7.80/1.50      ( k2_zfmisc_1(sK8,sK9) = k2_zfmisc_1(sK9,sK8) ),
% 7.80/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_20,plain,
% 7.80/1.50      ( ~ r2_hidden(X0,X1)
% 7.80/1.50      | ~ r2_hidden(X2,X3)
% 7.80/1.50      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 7.80/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_32137,plain,
% 7.80/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.80/1.50      | r2_hidden(X2,X3) != iProver_top
% 7.80/1.50      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 7.80/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_33683,plain,
% 7.80/1.50      ( r2_hidden(X0,sK9) != iProver_top
% 7.80/1.50      | r2_hidden(X1,sK8) != iProver_top
% 7.80/1.50      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK8,sK9)) = iProver_top ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_29,c_32137]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_21,plain,
% 7.80/1.50      ( r2_hidden(X0,X1)
% 7.80/1.50      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 7.80/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_32136,plain,
% 7.80/1.50      ( r2_hidden(X0,X1) = iProver_top
% 7.80/1.50      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 7.80/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_33909,plain,
% 7.80/1.50      ( r2_hidden(X0,sK9) != iProver_top
% 7.80/1.50      | r2_hidden(X1,sK9) = iProver_top
% 7.80/1.50      | r2_hidden(X1,sK8) != iProver_top ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_33683,c_32136]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_34341,plain,
% 7.80/1.50      ( r2_hidden(X0,sK9) = iProver_top
% 7.80/1.50      | r2_hidden(X0,sK8) != iProver_top
% 7.80/1.50      | v1_xboole_0(sK9) = iProver_top ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_32145,c_33909]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_27,negated_conjecture,
% 7.80/1.50      ( k1_xboole_0 != sK9 ),
% 7.80/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_4,plain,
% 7.80/1.50      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 7.80/1.50      inference(cnf_transformation,[],[f47]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_1108,plain,
% 7.80/1.50      ( ~ v1_xboole_0(sK9) | k1_xboole_0 = sK9 ),
% 7.80/1.50      inference(instantiation,[status(thm)],[c_4]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_1109,plain,
% 7.80/1.50      ( k1_xboole_0 = sK9 | v1_xboole_0(sK9) != iProver_top ),
% 7.80/1.50      inference(predicate_to_equality,[status(thm)],[c_1108]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_34362,plain,
% 7.80/1.50      ( r2_hidden(X0,sK8) != iProver_top
% 7.80/1.50      | r2_hidden(X0,sK9) = iProver_top ),
% 7.80/1.50      inference(global_propositional_subsumption,
% 7.80/1.50                [status(thm)],
% 7.80/1.50                [c_34341,c_27,c_1109]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_34363,plain,
% 7.80/1.50      ( r2_hidden(X0,sK9) = iProver_top
% 7.80/1.50      | r2_hidden(X0,sK8) != iProver_top ),
% 7.80/1.50      inference(renaming,[status(thm)],[c_34362]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_34370,plain,
% 7.80/1.50      ( r2_hidden(sK0(sK8),sK9) = iProver_top
% 7.80/1.50      | v1_xboole_0(sK8) = iProver_top ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_32145,c_34363]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_28,negated_conjecture,
% 7.80/1.50      ( k1_xboole_0 != sK8 ),
% 7.80/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_1822,plain,
% 7.80/1.50      ( ~ v1_xboole_0(sK8) | k1_xboole_0 = sK8 ),
% 7.80/1.50      inference(instantiation,[status(thm)],[c_4]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_1823,plain,
% 7.80/1.50      ( k1_xboole_0 = sK8 | v1_xboole_0(sK8) != iProver_top ),
% 7.80/1.50      inference(predicate_to_equality,[status(thm)],[c_1822]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_34777,plain,
% 7.80/1.50      ( r2_hidden(sK0(sK8),sK9) = iProver_top ),
% 7.80/1.50      inference(global_propositional_subsumption,
% 7.80/1.50                [status(thm)],
% 7.80/1.50                [c_34370,c_28,c_1823]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_32628,plain,
% 7.80/1.50      ( r2_hidden(X0,sK8) = iProver_top
% 7.80/1.50      | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK8,sK9)) != iProver_top ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_29,c_32136]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_33685,plain,
% 7.80/1.50      ( r2_hidden(X0,sK9) != iProver_top
% 7.80/1.50      | r2_hidden(X1,sK8) != iProver_top
% 7.80/1.50      | r2_hidden(X0,sK8) = iProver_top ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_32137,c_32628]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_34783,plain,
% 7.80/1.50      ( r2_hidden(X0,sK8) != iProver_top
% 7.80/1.50      | r2_hidden(sK0(sK8),sK8) = iProver_top ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_34777,c_33685]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_1830,plain,
% 7.80/1.50      ( r2_hidden(sK0(sK8),sK8) | v1_xboole_0(sK8) ),
% 7.80/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_1831,plain,
% 7.80/1.50      ( r2_hidden(sK0(sK8),sK8) = iProver_top
% 7.80/1.50      | v1_xboole_0(sK8) = iProver_top ),
% 7.80/1.50      inference(predicate_to_equality,[status(thm)],[c_1830]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_34792,plain,
% 7.80/1.50      ( r2_hidden(sK0(sK8),sK8) = iProver_top ),
% 7.80/1.50      inference(global_propositional_subsumption,
% 7.80/1.50                [status(thm)],
% 7.80/1.50                [c_34783,c_28,c_1823,c_1831]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_2,plain,
% 7.80/1.50      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 7.80/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_32143,plain,
% 7.80/1.50      ( r1_tarski(X0,X1) = iProver_top
% 7.80/1.50      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 7.80/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_34118,plain,
% 7.80/1.50      ( r1_tarski(sK9,X0) = iProver_top
% 7.80/1.50      | r2_hidden(X1,sK8) != iProver_top
% 7.80/1.50      | r2_hidden(sK1(sK9,X0),sK8) = iProver_top ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_32143,c_33685]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_34799,plain,
% 7.80/1.50      ( r1_tarski(sK9,X0) = iProver_top
% 7.80/1.50      | r2_hidden(sK1(sK9,X0),sK8) = iProver_top ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_34792,c_34118]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_1,plain,
% 7.80/1.50      ( r1_tarski(X0,X1) | ~ r2_hidden(sK1(X0,X1),X1) ),
% 7.80/1.50      inference(cnf_transformation,[],[f46]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_32144,plain,
% 7.80/1.50      ( r1_tarski(X0,X1) = iProver_top
% 7.80/1.50      | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
% 7.80/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_35600,plain,
% 7.80/1.50      ( r1_tarski(sK9,sK8) = iProver_top ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_34799,c_32144]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_34371,plain,
% 7.80/1.50      ( r1_tarski(sK8,X0) = iProver_top
% 7.80/1.50      | r2_hidden(sK1(sK8,X0),sK9) = iProver_top ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_32143,c_34363]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_35104,plain,
% 7.80/1.50      ( r1_tarski(sK8,sK9) = iProver_top ),
% 7.80/1.50      inference(superposition,[status(thm)],[c_34371,c_32144]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_7,plain,
% 7.80/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.80/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_26,negated_conjecture,
% 7.80/1.50      ( sK8 != sK9 ),
% 7.80/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_5215,plain,
% 7.80/1.50      ( ~ r1_tarski(sK9,sK8) | ~ r1_tarski(sK8,sK9) ),
% 7.80/1.50      inference(resolution,[status(thm)],[c_7,c_26]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(c_5216,plain,
% 7.80/1.50      ( r1_tarski(sK9,sK8) != iProver_top
% 7.80/1.50      | r1_tarski(sK8,sK9) != iProver_top ),
% 7.80/1.50      inference(predicate_to_equality,[status(thm)],[c_5215]) ).
% 7.80/1.50  
% 7.80/1.50  cnf(contradiction,plain,
% 7.80/1.50      ( $false ),
% 7.80/1.50      inference(minisat,[status(thm)],[c_35600,c_35104,c_5216]) ).
% 7.80/1.50  
% 7.80/1.50  
% 7.80/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.80/1.50  
% 7.80/1.50  ------                               Statistics
% 7.80/1.50  
% 7.80/1.50  ------ Selected
% 7.80/1.50  
% 7.80/1.50  total_time:                             0.796
% 7.80/1.50  
%------------------------------------------------------------------------------
